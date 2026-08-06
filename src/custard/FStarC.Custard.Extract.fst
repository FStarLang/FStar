(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Custard.Extract

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Errors.Msg
open FStarC.Class.Show
open FStarC.Syntax.Syntax
open FStarC.Const
open FStarC.Custard.Syntax

module BU     = FStarC.Util
module Dep    = FStarC.Parser.Dep
module E      = FStarC.Errors
module Ident  = FStarC.Ident
module Loader = FStarC.Custard.Loader
module N      = FStarC.TypeChecker.Normalize
module PC     = FStarC.Parser.Const
module S      = FStarC.Syntax.Syntax
module SMap   = FStarC.SMap
module SS     = FStarC.Syntax.Subst
module TcEnv  = FStarC.TypeChecker.Env
module U      = FStarC.Syntax.Util

(* -------------------------------------------------------------------- *)
(* State                                                                *)
(* -------------------------------------------------------------------- *)

type state = {
  deps:    Dep.deps;
  env:     ref TcEnv.env;
  (* lid -> the IR name it was assigned.  Filled in *before* the definition is
     translated, so that a recursive occurrence finds it and stops. *)
  names:   SMap.t name;
  emitted: SMap.t decl;
  (* Emission order, reversed: a definition is appended once its body has been
     translated, so uses come after definitions. *)
  order:   ref (list string);
}

let init (deps:Dep.deps) (env:TcEnv.env) : ML state = {
  deps    = deps;
  env     = mk_ref env;
  names   = SMap.create 100;
  emitted = SMap.create 100;
  order   = mk_ref [];
}

let custard_norm_steps : list TcEnv.step = [
  TcEnv.AllowUnboundUniverses;
  TcEnv.EraseUniverses;
  TcEnv.Beta;
  TcEnv.Iota;
  TcEnv.Zeta;
  TcEnv.Primops;
  TcEnv.Eager_unfolding;
  TcEnv.Inlining;
  TcEnv.PureSubtermsWithinComputations;
  TcEnv.Unascribe;
  TcEnv.Unmeta;
  TcEnv.ForExtraction;
  TcEnv.UnfoldAttr [PC.tcnorm_attr];
  TcEnv.ReduceProjections;
]

(* -------------------------------------------------------------------- *)
(* Names                                                                *)
(* -------------------------------------------------------------------- *)

let name_of_lid (l:Ident.lident) : ML name = {
  ns   = List.map Ident.string_of_id (Ident.ns_of_lid l);
  id   = Ident.string_of_id (Ident.ident_of_lid l);
  uniq = 0;
  hint = None;
}

let name_of_bv (b:bv) : ML string =
  Ident.string_of_id b.ppname ^ "_" ^ show b.index

(* -------------------------------------------------------------------- *)
(* Loading                                                              *)
(* -------------------------------------------------------------------- *)

let tcenv (st:state) : ML TcEnv.env = !st.env

(* A definition may live in a module the driver never loaded; pull it in.  This
   is the on-demand part of section 4.1. *)
let ensure_lid_available (st:state) (l:Ident.lident) : ML unit =
  let m = Ident.nsstr l in
  if m <> "" && not (Loader.module_is_loaded (tcenv st) m) then
    st.env := Loader.ensure_loaded st.deps (tcenv st) m

(* -------------------------------------------------------------------- *)
(* Effects                                                              *)
(* -------------------------------------------------------------------- *)

let eff_of_lid (st:state) (l:Ident.lident) : ML eff =
  let l = TcEnv.norm_eff_name (tcenv st) l in
  if Ident.lid_equals l PC.effect_GHOST_lid
  || Ident.lid_equals l PC.effect_Ghost_lid
  then E_Ghost
  else if Ident.lid_equals l PC.effect_PURE_lid
       || Ident.lid_equals l PC.effect_Pure_lid
       || Ident.lid_equals l PC.effect_Tot_lid
  then E_Pure
  else E_Impure

(* -------------------------------------------------------------------- *)
(* Requests                                                             *)
(* -------------------------------------------------------------------- *)

(* Section 3.3, step 3: this is where the demand-driven loop lives.  M1 has no
   specialization, so the key is just the lid; M2 replaces it by a spec_key. *)
let rec request (st:state) (l:Ident.lident) : ML name =
  let key = Ident.string_of_lid l in
  match SMap.try_find st.names key with
  | Some nm -> nm
  | None ->
    let nm = name_of_lid l in
    (* Register before translating: a self-reference must find this name
       rather than loop. *)
    SMap.add st.names key nm;
    ensure_lid_available st l;
    match datacon_owner st l with
    | Some ty_lid ->
      (* A data constructor is part of its inductive's declaration, not a
         declaration of its own: request the type and emit nothing. *)
      let _ = request st ty_lid in
      nm
    | None ->
      let d = extract_lid st l nm in
      SMap.add st.emitted key d;
      st.order := key :: !st.order;
      nm

and datacon_owner (st:state) (l:Ident.lident) : ML (option Ident.lident) =
  match TcEnv.lookup_sigelt (tcenv st) l with
  | Some ({ sigel = Sig_datacon {ty_lid} }) -> Some ty_lid
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Types                                                                *)
(* -------------------------------------------------------------------- *)

and ty_of_typ (st:state) (t:typ) : ML cty =
  let t = SS.compress t in
  match t.n with
  | Tm_bvar b
  | Tm_name b -> TVar (name_of_bv b)

  | Tm_uinst (t, _) -> ty_of_typ st t

  | Tm_fvar fv -> ty_of_fv st fv []

  | Tm_arrow _ ->
    let bs, c = U.arrow_formals_comp t in
    let res = ty_of_typ st (U.comp_result c) in
    let e = eff_of_lid st (U.comp_effect_name c) in
    (* The effect belongs to the last arrow only; the intermediate ones are the
       pure arrows a curried function is made of. *)
    let rec build (bs:binders) : ML cty =
      match bs with
      | [] -> res
      | [b] -> TArrow (ty_of_typ st b.binder_bv.sort, e, res)
      | b :: bs -> TArrow (ty_of_typ st b.binder_bv.sort, E_Pure, build bs)
    in
    build bs

  | Tm_app _ ->
    let hd, args = U.head_and_args_full t in
    (match (U.un_uinst hd).n with
     | Tm_fvar fv -> ty_of_fv st fv (args |> List.filter (fun (_, q) -> not (S.is_aqual_implicit q))
                                          |> List.map fst)
     | _ -> TAny)

  | Tm_refine {b} -> ty_of_typ st b.sort
  | Tm_ascribed {tm} -> ty_of_typ st tm
  | Tm_meta {tm} -> ty_of_typ st tm

  (* A type in type position: this is where a higher-kinded or dependent type
     would land.  M1 does not represent those. *)
  | Tm_type _
  | _ -> TAny

and ty_of_fv (st:state) (fv:fv) (args:list term) : ML cty =
  let l = S.lid_of_fv fv in
  if Ident.lid_equals l PC.unit_lid then TUnit
  else TApp (request st l, List.map (ty_of_typ st) args)

(* -------------------------------------------------------------------- *)
(* Terms                                                                *)
(* -------------------------------------------------------------------- *)

and constant_of_sconst (c:sconst) : ML (option constant) =
  match c with
  | Const_unit -> Some CUnit
  | Const_bool b -> Some (CBool b)
  | Const_int (s, w) -> Some (CInt (s, w))
  | Const_char c -> Some (CChar c)
  | Const_string (s, _) -> Some (CString s)
  | _ -> None

and ty_of_constant (st:state) (c:constant) : ML cty =
  match c with
  | CUnit -> TUnit
  | CBool _ -> TApp (request st PC.bool_lid, [])
  | CInt (_, None) -> TApp (request st PC.int_lid, [])
  | CInt (_, Some _) -> TAny
  | CChar _ -> TApp (request st PC.char_lid, [])
  | CString _ -> TApp (request st PC.string_lid, [])

and is_data_ctor (fv:fv) : ML bool =
  match fv.fv_qual with
  | Some Data_ctor
  | Some (Record_ctor _) -> true
  | _ -> false

and expr_of_term (st:state) (t:term) : ML expr =
  let t = SS.compress t in
  match t.n with
  | Tm_constant c ->
    (match constant_of_sconst c with
     | Some c -> mk (EConst c) (ty_of_constant st c) E_Pure
     | None -> unit_expr)

  | Tm_bvar b
  | Tm_name b -> mk (EVar (name_of_bv b)) (ty_of_typ st b.sort) E_Pure

  | Tm_uinst (t, _) -> expr_of_term st t

  | Tm_fvar fv -> expr_of_fv st fv []

  | Tm_abs _ ->
    let bs, body, _ = U.abs_formals t in
    let bs = bs |> List.filter (fun b -> not (S.is_bqual_implicit b.binder_qual)) in
    let body = expr_of_term st body in
    let bs = bs |> List.map (fun b ->
      { b_name = name_of_bv b.binder_bv; b_ty = ty_of_typ st b.binder_bv.sort }) in
    (match bs with
     | [] -> body
     | _ -> mk (EFun (bs, body)) TAny E_Pure)

  | Tm_app _ ->
    let hd, args = U.head_and_args_full t in
    let args = args |> List.filter (fun (a, q) ->
                 not (S.is_aqual_implicit q) && not (is_type_arg a))
                    |> List.map fst in
    let args = args |> List.map (expr_of_term st) in
    (match (U.un_uinst hd).n with
     | Tm_fvar fv -> apply st (expr_of_fv st fv args) fv args
     | _ ->
       let hd = expr_of_term st hd in
       (match args with
        | [] -> hd
        | _ -> mk (EApp (hd, args)) TAny (List.fold_left (fun e a -> join_eff e a.eff) hd.eff args)))

  | Tm_let {lbs=(false, [lb]); body} ->
    (match lb.lbname with
     | Inl bv ->
       let bv, body = SS.open_term_bv bv body in
       let e1 = expr_of_term st lb.lbdef in
       let e2 = expr_of_term st body in
       mk (ELet (name_of_bv bv, ty_of_typ st lb.lbtyp, e1, e2)) e2.ty (join_eff e1.eff e2.eff)
     | Inr _ ->
       (* A top-level binding cannot appear here. *)
       expr_of_term st body)

  | Tm_match {scrutinee; brs} ->
    let scrut = expr_of_term st scrutinee in
    let brs = brs |> List.map (branch_of_branch st) in
    let e = List.fold_left (fun e (_, g, b) ->
              join_eff e (join_eff b.eff (match g with None -> E_Pure | Some g -> g.eff)))
              scrut.eff brs in
    let ty = match brs with [] -> TAny | (_, _, b) :: _ -> b.ty in
    mk (EMatch (scrut, brs)) ty e

  | Tm_ascribed {tm} -> expr_of_term st tm
  | Tm_meta {tm} -> expr_of_term st tm

  (* Types and proofs in term position are erased. *)
  | Tm_type _ -> unit_expr
  | _ -> unit_expr

and is_type_arg (a:term) : ML bool =
  match (SS.compress a).n with
  | Tm_type _ -> true
  | _ -> false

and expr_of_fv (st:state) (fv:fv) (args:list expr) : ML expr =
  let l = S.lid_of_fv fv in
  if is_data_ctor fv
  then mk (ECtor (request st l, args)) TAny E_Pure
  else mk (EQual (request st l, [])) TAny E_Pure

and apply (st:state) (hd:expr) (fv:fv) (args:list expr) : ML expr =
  match hd.e, args with
  | ECtor _, _ -> hd            (* expr_of_fv already applied the arguments *)
  | _, [] -> hd
  | _, _ ->
    let e = List.fold_left (fun e a -> join_eff e a.eff) (callee_eff st fv) args in
    mk (EApp (hd, args)) TAny e

(* The effect of calling [fv]: we know it exactly, because the callee has
   already been extracted by the time we get here (requests are depth-first). *)
and callee_eff (st:state) (fv:fv) : ML eff =
  match SMap.try_find st.emitted (Ident.string_of_lid (S.lid_of_fv fv)) with
  | Some (DLet l) -> l.dl_eff
  | Some (DExternal _) -> E_Impure
  | _ -> E_Pure

and branch_of_branch (st:state) (br:S.branch) : ML branch =
  let p, g, b = SS.open_branch br in
  (pat_of_pat st p,
   (match g with None -> None | Some g -> Some (expr_of_term st g)),
   expr_of_term st b)

and pat_of_pat (st:state) (p:S.pat) : ML pat =
  match p.v with
  | Pat_constant c ->
    (match constant_of_sconst c with
     | Some c -> PConst c
     | None -> PWild)
  | Pat_var bv -> PVar (name_of_bv bv)
  | Pat_dot_term _ -> PWild
  | Pat_cons (fv, _, pats) ->
    let pats = pats |> List.filter (fun (_, imp) -> not imp)
                    |> List.map (fun (p, _) -> pat_of_pat st p) in
    PCtor (request st (S.lid_of_fv fv), pats)

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

and extract_lid (st:state) (l:Ident.lident) (nm:name) : ML decl =
  match TcEnv.lookup_sigelt (tcenv st) l with
  | None ->
    E.raise_error0 E.Error_CustardEntryNotFound [
      text ("Custard cannot find a definition for " ^ Ident.string_of_lid l ^ ".")
    ]
  | Some se -> extract_sigelt st l nm se

and extract_sigelt (st:state) (l:Ident.lident) (nm:name) (se:sigelt) : ML decl =
  match se.sigel with
  | Sig_let {lbs=(is_rec, lbs)} ->
    (match lbs |> List.tryFind (fun lb ->
             match lb.lbname with
             | Inr fv -> Ident.lid_equals (S.lid_of_fv fv) l
             | Inl _ -> false) with
     | Some lb ->
       (* A type abbreviation is a [Sig_let] too; it must not become a value. *)
       if is_type_sig st lb.lbtyp
       then extract_type_abbrev st nm lb
       else extract_letbinding st nm lb is_rec
     | None -> DExternal { dx_name = nm; dx_ty = TAny; dx_flags = [] })

  | Sig_declare_typ {t} ->
    (* An [assume val], or a type whose definition is not available: an
       external symbol, to be realized by the backend or by a custom rule
       (section 8). *)
    if is_type_sig st t
    then DType { dt_name = nm; dt_params = []; dt_body = TAbstract; dt_flags = [] }
    else DExternal { dx_name = nm; dx_ty = ty_of_typ st t; dx_flags = [] }

  | Sig_inductive_typ {us; params} ->
    extract_inductive st l nm params

  | Sig_datacon _ ->
    (* Reached through a constructor application or pattern: what we actually
       want is the type it belongs to, which the layout analysis (M3) will
       need.  For now record it as external so the name exists. *)
    DExternal { dx_name = nm; dx_ty = TAny; dx_flags = [] }

  | Sig_bundle {ses} ->
    (match ses |> List.tryFind (fun se ->
             match se.sigel with
             | Sig_inductive_typ {lid} -> Ident.lid_equals lid l
             | _ -> false) with
     | Some se -> extract_sigelt st l nm se
     | None -> DType { dt_name = nm; dt_params = []; dt_body = TAbstract; dt_flags = [] })

  | _ ->
    DExternal { dx_name = nm; dx_ty = TAny; dx_flags = [] }

(* [eqtype], [Type0] and friends are all abbreviations, so we have to unfold
   before we can tell a type declaration from a value declaration. *)
and is_type_sig (st:state) (t:typ) : ML bool =
  let _, c = U.arrow_formals_comp t in
  let res = N.normalize [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                         TcEnv.Beta; TcEnv.Iota;
                         TcEnv.UnfoldUntil delta_constant]
                        (tcenv st) (U.comp_result c) in
  (* [eqtype] is a refinement of [Type0], so peel refinements too. *)
  let rec is_type (t:typ) : ML bool =
    match (SS.compress t).n with
    | Tm_type _ -> true
    | Tm_refine {b} -> is_type b.sort
    | _ -> false
  in
  is_type res

and extract_type_abbrev (st:state) (nm:name) (lb:letbinding) : ML decl =
  let bs, body, _ = U.abs_formals lb.lbdef in
  DType {
    dt_name   = nm;
    dt_params = bs |> List.map (fun b -> name_of_bv b.binder_bv);
    dt_body   = TAbbrev (ty_of_typ st body);
    dt_flags  = [];
  }

and extract_letbinding (st:state) (nm:name) (lb:letbinding) (is_rec:bool) : ML decl =
  let def = N.normalize custard_norm_steps (tcenv st) lb.lbdef in
  let bs, body, _ = U.abs_formals def in
  let bs = bs |> List.filter (fun b -> not (S.is_bqual_implicit b.binder_qual)) in
  let binders = bs |> List.map (fun b ->
    { b_name = name_of_bv b.binder_bv; b_ty = ty_of_typ st b.binder_bv.sort }) in
  (* The effect is the one of the *codomain*: [lbeff] is the effect of
     evaluating the lambda, which is always Tot. *)
  let _, c = U.arrow_formals_comp lb.lbtyp in
  let eff = eff_of_lid st (U.comp_effect_name c) in
  let ret = ty_of_typ st (U.comp_result c) in
  DLet {
    dl_name    = nm;
    dl_typars  = [];
    dl_binders = binders;
    dl_ret     = ret;
    dl_eff     = eff;
    dl_body    = expr_of_term st body;
    (* M1 has no SCC analysis yet, so a recursive definition is its own group;
       mutual recursion is handled in a later milestone. *)
    dl_flags   = (if is_rec then [Rec [nm]] else []);
  }

and extract_inductive (st:state) (l:Ident.lident) (nm:name) (params:binders) : ML decl =
  let _, ctors = TcEnv.datacons_of_typ (tcenv st) l in
  let params = params |> List.map (fun b -> name_of_bv b.binder_bv) in
  let ctor (c:Ident.lident) : ML (name & list (string & cty)) =
    let _, ty = TcEnv.lookup_datacon (tcenv st) c in
    let bs, _ = U.arrow_formals_comp ty in
    (* Drop the inductive's own parameters, which are re-bound by every
       constructor's type. *)
    let bs = if List.length bs >= List.length params
             then List.splitAt (List.length params) bs |> snd
             else bs in
    (name_of_lid c,
     bs |> List.map (fun b ->
       (name_of_bv b.binder_bv, ty_of_typ st b.binder_bv.sort)))
  in
  DType {
    dt_name   = nm;
    dt_params = params;
    dt_body   = TVariant (ctors |> List.map ctor);
    dt_flags  = [];
  }

(* -------------------------------------------------------------------- *)
(* Driving                                                              *)
(* -------------------------------------------------------------------- *)

let run (st:state) (roots:list Ident.lident) : ML program =
  roots |> List.iter (fun l ->
    let nm = request st l in
    (* Mark the root so backends know which symbols must survive. *)
    match SMap.try_find st.emitted (Ident.string_of_lid l) with
    | Some (DLet d) ->
      SMap.add st.emitted (Ident.string_of_lid l)
               (DLet { d with dl_flags = Entrypoint :: d.dl_flags })
    | _ -> ());
  List.rev !st.order |> List.collect (fun key ->
    match SMap.try_find st.emitted key with
    | Some d -> [d]
    | None -> [])
