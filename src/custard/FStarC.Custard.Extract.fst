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
open FStarC.Class.Setlike
open FStarC.Syntax.Syntax
open FStarC.Syntax.Print
open FStarC.Const
open FStarC.Custard.Mono

open FStarC.Custard.Syntax

module BU     = FStarC.Format
module Dep    = FStarC.Parser.Dep
module E      = FStarC.Errors
module Effects = FStarC.Custard.Effects
module Free   = FStarC.Syntax.Free
module Ident  = FStarC.Ident
module Loader = FStarC.Custard.Loader
module Mono   = FStarC.Custard.Mono
module Builtins = FStarC.Custard.Builtins
module GenSym = FStarC.GenSym
module N      = FStarC.TypeChecker.Normalize
module PC     = FStarC.Parser.Const
module ExtractAs = FStarC.Parser.Const.ExtractAs
module S      = FStarC.Syntax.Syntax
module SMap   = FStarC.SMap
module SS     = FStarC.Syntax.Subst
module TcEnv  = FStarC.TypeChecker.Env
module U      = FStarC.Syntax.Util

(* -------------------------------------------------------------------- *)
(* Specialization keys                                                  *)
(* -------------------------------------------------------------------- *)

(* Section 3.7: two call sites share a specialization when their [Mono]
   arguments have the same canonical form.  This step list is deliberately much
   smaller than the one used on a definition's body: the key only has to make
   equal things syntactically equal.

   [Primops] is what makes [loop_unrolling (n-1)] fold to a literal, without
   which every recursive call would produce a fresh key.  Delta-unfolding is
   what turns a named type-class instance into a concrete dictionary value, so
   that [ReduceProjections] can collapse method projections in the body. *)
let key_norm_steps : list TcEnv.step = [
  TcEnv.AllowUnboundUniverses;
  TcEnv.EraseUniverses;
  TcEnv.Beta;
  TcEnv.Iota;
  TcEnv.Primops;
  TcEnv.Unascribe;
  TcEnv.Unmeta;
  TcEnv.UnfoldUntil delta_constant;
]

let string_of_key (k:spec_key) : ML string =
  Ident.string_of_lid k.sk_lid ^
  (k.sk_args |> List.map (fun (i, t) -> "#" ^ show i ^ "=" ^ show t)
             |> String.concat "")

(* -------------------------------------------------------------------- *)
(* State                                                                *)
(* -------------------------------------------------------------------- *)

type state = {
  deps:    Dep.deps;
  env:     ref TcEnv.env;
  (* Specialization key -> the IR name it was assigned.  Filled in *before*
     the definition is translated, so that a recursive occurrence finds it and
     stops. *)
  names:   SMap.t name;
  emitted: SMap.t decl;
  (* Emission order, reversed: a definition is appended once its body has been
     translated, so uses come after definitions. *)
  order:   ref (list string);
  (* lid -> its binder classification (section 3.1), computed once. *)
  classes: SMap.t (list bclass);
  (* lid -> how many specializations of it we have created so far. *)
  counts:  SMap.t int;
  (* The mangled names handed out already, so that two specializations whose
     hints coincide still get distinct names. *)
  suffixes: SMap.t bool;
  fuel:    ref int;
  (* The chain of requests that led to what we are currently working on,
     innermost first.  Only used to make diagnostics debuggable (section
     3.6). *)
  chain:   ref (list string);
}

let init (deps:Dep.deps) (env:TcEnv.env) : ML state = {
  deps    = deps;
  env     = mk_ref env;
  names   = SMap.create 100;
  emitted = SMap.create 100;
  order   = mk_ref [];
  classes = SMap.create 100;
  counts  = SMap.create 100;
  suffixes = SMap.create 100;
  fuel    = mk_ref (Options.custard_fuel ());
  chain   = mk_ref [];
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
  (* [tcmethod] inlines a class's method accessor down to the record
     projection, which [ReduceProjections] then collapses against the concrete
     dictionary: no method projector survives into the IR (section 3.4). *)
  TcEnv.UnfoldAttr [PC.tcnorm_attr; PC.tcmethod_lid];
  TcEnv.ReduceProjections;
]

let tcenv (st:state) : ML TcEnv.env = !st.env

(* -------------------------------------------------------------------- *)
(* Diagnostics                                                          *)
(* -------------------------------------------------------------------- *)

(* Every Custard error is reported with the chain of specialization requests
   that reached it: without it a failure deep inside a specialized library
   function is impossible to act on. *)
let chain_display_limit : int = 10

let request_chain (st:state) : ML (list Pprint.document) =
  match !st.chain with
  | [] -> []
  | c ->
    let n = List.length c in
    let shown, elided =
      if n <= chain_display_limit
      then c, []
      else List.splitAt chain_display_limit c |> fst,
           [text ("... and " ^ show (n - chain_display_limit) ^ " more.")]
    in
    [text "Reached through:"] @
    (shown |> List.map (fun s -> Pprint.doc_of_string ("  " ^ s))) @
    elided

let custard_error (#a:Type) (st:state) (code:E.error_code) (msg:list Pprint.document) : ML a =
  E.raise_error0 code (msg @ request_chain st)

(* -------------------------------------------------------------------- *)
(* Loading                                                              *)
(* -------------------------------------------------------------------- *)

(* A definition may live in a module the driver never loaded; pull it in.  This
   is the on-demand part of section 4.1. *)
let ensure_lid_available (st:state) (l:Ident.lident) : ML unit =
  let m = Ident.nsstr l in
  if m <> "" && not (Loader.module_is_loaded st.deps (tcenv st) m) then
    st.env := Loader.ensure_loaded st.deps (tcenv st) m

(* -------------------------------------------------------------------- *)
(* Names                                                                *)
(* -------------------------------------------------------------------- *)

let name_of_lid (l:Ident.lident) : ML name = {
  ns   = List.map Ident.string_of_id (Ident.ns_of_lid l);
  id   = Ident.string_of_id (Ident.ident_of_lid l);
  spec = None;
}

let name_of_bv (b:bv) : ML string =
  Ident.string_of_id b.ppname ^ "_" ^ show b.index

(* A readable suffix for a specialization: the head symbol of its first [Mono]
   argument is almost always the interesting one (the type, or the instance). *)
let hint_of_args (args:list (int & term)) : ML (option string) =
  match args with
  | [] -> None
  | (_, t) :: _ ->
    let hd, _ = U.head_and_args_full t in
    (match (U.un_uinst (SS.compress hd)).n with
     | Tm_fvar fv -> Some (Ident.string_of_id (Ident.ident_of_lid (S.lid_of_fv fv)))
     | Tm_constant (Const_int (s, _)) -> Some s
     | Tm_constant (Const_bool b) -> Some (if b then "true" else "false")
     | _ -> None)

(* The suffix that distinguishes one specialization of [lstr] from its
   siblings.  A definition that was not specialized at all keeps its bare
   name; every specialization gets a suffix, even when it turns out to be the
   only one, so that a name means the same thing regardless of how many
   siblings happen to exist.  The readable hint is preferred, and falls back
   to the sequence number when it is missing or already taken. *)
let spec_suffix (st:state) (lstr:string) (args:list (int & term)) (n:int)
  : ML (option string) =
  if Nil? args then None
  else
    let claim (s:string) : ML bool =
      let key = lstr ^ "__" ^ s in
      if Some? (SMap.try_find st.suffixes key) then false
      else (SMap.add st.suffixes key true; true) in
    match hint_of_args args with
    | Some h when claim h -> Some h
    | Some h -> Some (h ^ "_" ^ show n)
    | None -> Some (show n)

(* -------------------------------------------------------------------- *)
(* Effects                                                              *)
(* -------------------------------------------------------------------- *)

let eff_of_comp (st:state) (c:comp) : ML eff = Effects.of_comp (tcenv st) c

(* Applying [n] arguments to something of type [ty] runs the effects of the
   first [n] arrows.  This is how a call through a *variable* -- a function
   parameter, or a local closure -- gets its effect: there is no declaration to
   consult, only the type.  When the type is not arrow-shaped (typically
   [TAny]) we have to assume the worst, or section 7.3 would let us drop a call
   we know nothing about. *)
let rec apply_eff (ty:cty) (n:int) : ML eff =
  if n <= 0 then E_Pure
  else
    match ty with
    | TArrow (_, e, r) -> join_eff e (apply_eff r (n - 1))
    | _ -> E_Impure

let rec apply_result (ty:cty) (n:int) : ML cty =
  if n <= 0 then ty
  else
    match ty with
    | TArrow (_, _, r) -> apply_result r (n - 1)
    | _ -> TAny

(* -------------------------------------------------------------------- *)
(* Requests                                                             *)
(* -------------------------------------------------------------------- *)

(* Section 3.3, step 3: this is where the demand-driven loop lives. *)
let rec request (st:state) (k:spec_key) : ML name =
  let key = string_of_key k in
  match SMap.try_find st.names key with
  | Some nm -> nm
  | None ->
    check_budget st k;
    let l = k.sk_lid in
    let lstr = Ident.string_of_lid l in
    let n = (match SMap.try_find st.counts lstr with None -> 0 | Some n -> n) in
    SMap.add st.counts lstr (n + 1);
    let nm = { name_of_lid l with spec = spec_suffix st lstr k.sk_args n } in
    (* Register before translating: a self-reference must find this name
       rather than loop. *)
    SMap.add st.names key nm;
    ensure_lid_available st l;
    match datacon_owner st l with
    | Some ty_lid ->
      (* A data constructor is part of its inductive's declaration, not a
         declaration of its own: request the type and emit nothing. *)
      let _ = request st { sk_lid = ty_lid; sk_args = [] } in
      nm
    | None ->
      let saved = !st.chain in
      st.chain := key :: saved;
      let d = extract_lid st l nm k.sk_args in
      st.chain := saved;
      SMap.add st.emitted key d;
      st.order := key :: !st.order;
      nm

(* Section 3.6: the budget is checked *before* the definition is looked up and
   before its body is normalized, so that a diverging specialization is cut off
   after a negligible amount of work. *)
and check_budget (st:state) (k:spec_key) : ML unit =
  let lstr = Ident.string_of_lid k.sk_lid in
  let n = match SMap.try_find st.counts lstr with None -> 0 | Some n -> n in
  if n >= Options.custard_max_specializations () then
    custard_error st E.Error_CustardFuelExhausted [
      text ("Custard created " ^ show n ^ " specializations of " ^ lstr ^
            ", which is the limit set by --custard_max_specializations.");
      text "This usually means a definition recurses through a monomorphized \
            binder. Use --custard_dump_specializations to see which \
            definitions are being specialized."
    ];
  st.fuel := !st.fuel - 1;
  if !st.fuel <= 0 then
    custard_error st E.Error_CustardFuelExhausted [
      text ("Custard ran out of specialization fuel while requesting " ^ lstr ^
            "; see --custard_fuel.")
    ]

and datacon_owner (st:state) (l:Ident.lident) : ML (option Ident.lident) =
  match TcEnv.lookup_sigelt (tcenv st) l with
  | Some ({ sigel = Sig_datacon {ty_lid} }) -> Some ty_lid
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Binder classification                                                *)
(* -------------------------------------------------------------------- *)

(* Section 3.1.  Computed once per definition and cached: it is a property of
   the definition, not of a call site. *)
and binder_classes (st:state) (l:Ident.lident) : ML (list bclass) =
  let key = Ident.string_of_lid l in
  match SMap.try_find st.classes key with
  | Some cs -> cs
  | None ->
    ensure_lid_available st l;
    let cs =
      match TcEnv.lookup_sigelt (tcenv st) l with
      | Some se ->
        (match se.sigel with
         | Sig_let {lbs=(_, lbs)} ->
           (match lbs |> List.tryFind (fun lb ->
                    match lb.lbname with
                    | Inr fv -> Ident.lid_equals (S.lid_of_fv fv) l
                    | Inl _ -> false) with
            | Some lb -> classify (tcenv st) (se.sigattrs @ lb.lbattrs) lb.lbtyp
            | None -> [])
         | Sig_declare_typ {t} -> classify (tcenv st) se.sigattrs t
         | _ -> [])
      | None -> []
    in
    SMap.add st.classes key cs;
    cs

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
    (* Section 7.2: a codomain of the form [stt b p q] contributes [b] as the
       result type and promotes the arrow to [E_Impure]. *)
    let res = ty_of_typ st (Effects.result_typ (tcenv st) c) in
    let e = eff_of_comp st c in
    let bs = drop_flagged (Mono.erased_binders (tcenv st) t) bs in
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
    (match Effects.impure_effect_result (tcenv st) t with
     (* Section 7.2, rule 1: [stt b p q] is represented by [b]. *)
     | Some a -> ty_of_typ st a
     | None ->
       let hd, args = U.head_and_args_full t in
       (match (U.un_uinst hd).n with
        | Tm_fvar fv ->
          (* A type constructor's arguments survive into the [cty] exactly when
             they are types: an index like the [n] of [vec n] has no
             counterpart in the target's type language. *)
          let keep = match TcEnv.try_lookup_lid (tcenv st) (S.lid_of_fv fv) with
                     | Some ((_, k), _) -> Mono.type_binders (tcenv st) k
                                           |> List.map (fun b -> not b)
                     | None -> [] in
          ty_of_fv st fv (drop_flagged keep args |> List.map fst)
        | _ -> TAny))

  | Tm_refine {b} -> ty_of_typ st b.sort
  | Tm_ascribed {tm} -> ty_of_typ st tm
  | Tm_meta {tm} -> ty_of_typ st tm

  (* A type in type position: this is where a higher-kinded or dependent type
     would land.  M1 does not represent those. *)
  | Tm_type _
  | _ -> TAny

(* Type constructors are compiled uniformly in their parameters (section 5.0),
   so an inductive is never specialized: it is always requested with an empty
   key. *)
and ty_of_fv (st:state) (fv:fv) (args:list term) : ML cty =
  let l = S.lid_of_fv fv in
  if Ident.lid_equals l PC.unit_lid then TUnit
  else
    let args = List.map (ty_of_typ st) args in
    (* Section 8: a type with a custom rule has a representation fixed outside
       F*, so it is never requested and its F* definition is never seen. *)
    match Builtins.lookup_rule l with
    | Some (Builtins.Rule_type f) -> f args
    | _ -> TApp (request st { sk_lid = l; sk_args = [] }, args)

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
  let prim (l:Ident.lident) : ML cty = TApp (request st { sk_lid = l; sk_args = [] }, []) in
  match c with
  | CUnit -> TUnit
  | CBool _ -> prim PC.bool_lid
  | CInt (_, None) -> prim PC.int_lid
  | CInt (_, Some sw) -> TInt sw
  | CChar _ -> prim PC.char_lid
  | CString _ -> prim PC.string_lid

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

  | Tm_fvar fv -> app_of_fv st fv []

  | Tm_abs _ ->
    let bs, body, _ = U.abs_formals t in
    let body = expr_of_term st body in
    let bs =
      let flags = bs |> List.map (Mono.is_erased_binder (tcenv st)) in
      (* Same guard as [Mono.erased_binders]: a lambda whose binders all vanish
         would become a value, running its effects where it is built. *)
      let flags = if List.for_all (fun b -> b) flags && not (is_pure body.eff)
                  then (match List.rev flags with
                        | _ :: r -> List.rev (false :: r)
                        | [] -> flags)
                  else flags in
      drop_flagged flags bs in
    let bs = bs |> List.map (fun b ->
      { b_name = name_of_bv b.binder_bv; b_ty = ty_of_typ st b.binder_bv.sort }) in
    (match bs with
     | [] -> body
     | _ ->
       (* Give the lambda an arrow type: it is what tells a caller reached
          through a variable which effects applying it will run (section 7.3). *)
       let ty = List.fold_right (fun b (ty, e) -> (TArrow (b.b_ty, e, ty), E_Pure))
                                bs (body.ty, body.eff) |> fst in
       mk (EFun (bs, body)) ty E_Pure)

  | Tm_app _ ->
    let hd, args = U.head_and_args_full t in
    (match (U.un_uinst hd).n with
     | Tm_fvar fv -> app_of_fv st fv args
     | _ ->
       let hd_term = hd in
       let hd = expr_of_term st hd in
       (* No declaration to consult, so the filter has to come from the head's
          own type; a head we cannot type is left alone. *)
       let flags = match (SS.compress hd_term).n with
                   | Tm_name bv -> Mono.erased_binders (tcenv st) bv.sort
                   | _ -> [] in
       let args = drop_flagged flags args |> List.map fst |> List.map (expr_of_term st) in
       (match args with
        | [] -> hd
        | _ ->
          let n = List.length args in
          let e = List.fold_left (fun e a -> join_eff e a.eff)
                                 (join_eff hd.eff (apply_eff hd.ty n)) args in
          mk (EApp (hd, args)) (apply_result hd.ty n) e))

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

(* Delete the entries flagged [true].  A flag list shorter than the list being
   filtered leaves the surplus entries alone, which is what we want when a
   spine is longer than its head's declared arity.

   Note there is no test on implicit/explicit anywhere in Custard: whether an
   argument was written by the user or inferred says nothing about whether it
   has to exist at runtime, and unlike the ML extraction we have no
   interoperability reason to preserve the source arity. *)
(* The complement of {!drop_flagged}: keep exactly the entries flagged [true].
   A flag list shorter than the list keeps nothing of the surplus. *)
and keep_flagged (#a:Type) (flags:list bool) (xs:list a) : ML (list a) =
  match flags, xs with
  | _, [] -> []
  | [], _ -> []
  | f :: flags, x :: xs ->
    let rest = keep_flagged flags xs in
    if f then x :: rest else rest

and drop_flagged (#a:Type) (flags:list bool) (xs:list a) : ML (list a) =
  match flags, xs with
  | _, [] -> []
  | [], xs -> xs
  | f :: flags, x :: xs ->
    let rest = drop_flagged flags xs in
    if f then rest else x :: rest

(* -------------------------------------------------------------------- *)
(* Call sites                                                           *)
(* -------------------------------------------------------------------- *)

(* The core of monomorphization: split a call's arguments into the [Mono] ones,
   which become part of the specialization key, and the rest, which are passed
   at runtime. *)
and app_of_fv (st:state) (fv:fv) (args:args) : ML expr =
  let l = S.lid_of_fv fv in
  match Builtins.lookup_rule l with
  | Some (Builtins.Rule_prim (n, f)) -> prim_app st l n f args
  | _ -> app_of_fv' st fv args

(* A primitive is a function in F* but an operator in the IR, so an
   under-applied use has to be eta-expanded rather than passed along. *)
and prim_app (st:state) (l:Ident.lident) (n:int)
             (f : list cty -> list expr -> ML expr) (args:args) : ML expr =
  let decl_ty = match TcEnv.try_lookup_lid (tcenv st) l with
                | Some ((_, ty), _) -> Some ty
                | None -> None in
  let flags = match decl_ty with
              | Some ty -> Mono.erased_binders (tcenv st) ty
              | None -> [] in
  (* A rule that builds a buffer, a null pointer or a cast needs to know at
     which type; the type arguments are erased from the value spine, so they
     are collected separately rather than reconstructed from it. *)
  let tyargs = match decl_ty with
               | Some ty ->
                 keep_flagged (Mono.type_binders (tcenv st) ty) args
                 |> List.map fst |> List.map (ty_of_typ st)
               | None -> [] in
  let args = drop_flagged flags args |> List.map fst |> List.map (expr_of_term st) in
  let given, extra =
    if List.length args <= n then args, []
    else List.splitAt n args in
  let missing = n - List.length given in
  if missing > 0
  then
    let bs = List.map (fun _ -> { b_name = "custard_eta_" ^ show (GenSym.next_id ());
                                  b_ty = TAny })
                      (repeat_unit missing) in
    let vs = bs |> List.map (fun b -> mk (EVar b.b_name) b.b_ty E_Pure) in
    let body = f tyargs (given @ vs) in
    mk (EFun (bs, body))
       (List.fold_right (fun (b:binder) t -> TArrow (b.b_ty, E_Pure, t)) bs body.ty)
       E_Pure
  else
    let e = f tyargs given in
    match extra with
    | [] -> e
    | _ -> mk (EApp (e, extra)) (apply_result e.ty (List.length extra))
              (List.fold_left (fun x a -> join_eff x a.eff)
                              (apply_eff e.ty (List.length extra)) extra)

and repeat_unit (n:int) : ML (list unit) =
  if n <= 0 then [] else () :: repeat_unit (n - 1)

and app_of_fv' (st:state) (fv:fv) (args:args) : ML expr =
  let l = S.lid_of_fv fv in
  ensure_lid_available st l;
  if is_data_ctor fv
  then
    let nm = request st { sk_lid = l; sk_args = [] } in
    let flags = match TcEnv.try_lookup_lid (tcenv st) l with
                | Some ((_, ty), _) -> Mono.erased_binders (tcenv st) ty
                | None -> [] in
    mk (ECtor (nm, drop_flagged flags args |> List.map fst |> List.map (expr_of_term st)))
       (ctor_result_ty st l args) E_Pure
  else
    let cs = binder_classes st l in
    let margs, rest = split_mono_args st l cs args in
    let key = { sk_lid = l; sk_args = margs } in
    let nm = request st key in
    (* Uniform compilation (section 5.0) deletes the type arguments from the
       value spine, but the karamel backend still needs them: it is karamel's
       own monomorphization that turns a polymorphic Custard declaration into C.
       So they are carried on the [EQual] node instead, as a type application. *)
    let tyargs = call_type_args st l cs args in
    let hd_ty = callee_sig st (string_of_key key) tyargs in
    let hd = mk (EQual (nm, tyargs)) hd_ty E_Pure in
    (* [split_mono_args] has already removed the [Mono] and [Dropped]
       arguments, so everything left is passed at runtime. *)
    let rest = rest |> List.map fst |> List.map (expr_of_term st) in
    match rest with
    | [] -> hd
    | _ ->
      let e = List.fold_left (fun e a -> join_eff e a.eff)
                             (callee_eff st (string_of_key key) (List.length rest)) rest in
      mk (EApp (hd, rest)) (apply_result hd_ty (List.length rest)) e

(* A constructor application's type is the constructor's result type with the
   inductive's parameters instantiated -- which the spine supplies, since the
   parameters come first.  karamel needs it: [ECons] carries the type of the
   value being built, and an [any] there makes its datatype passes fail. *)
and ctor_result_ty (st:state) (l:Ident.lident) (spine:args) : ML cty =
  match TcEnv.try_lookup_lid (tcenv st) l with
  | None -> TAny
  | Some ((_, ty), _) ->
    let bs, c = U.arrow_formals_comp ty in
    let rec go (bs:binders) (sp:args) (acc:list subst_elt) : ML (list subst_elt) =
      match bs, sp with
      | b :: bs, (a, _) :: sp -> go bs sp (NT (b.binder_bv, a) :: acc)
      | _ -> acc in
    ty_of_typ st (SS.subst (go bs spine []) (U.comp_result c))

(* The type arguments of a call, in the order [extract_letbinding] records them
   in [dl_typars]: source order, restricted to the type binders that survived
   as parameters rather than being specialized away. *)
and call_type_args (st:state) (l:Ident.lident) (cs:list bclass) (spine:args) : ML (list cty) =
  let tflags = match TcEnv.try_lookup_lid (tcenv st) l with
               | Some ((_, ty), _) -> Mono.type_binders (tcenv st) ty
               | None -> [] in
  let rec go (cs:list bclass) (tf:list bool) (sp:args) : ML (list cty) =
    match cs, tf, sp with
    | c :: cs, t :: tf, (a, _) :: sp ->
      if t && not (Mono? c)
      then ty_of_typ st a :: go cs tf sp
      else go cs tf sp
    | _ -> [] in
  go cs tflags spine

(* The callee's signature, instantiated at this call site.  It is available
   because requests are depth-first; a recursive call is the exception, and
   falls back to [TAny]. *)
and callee_sig (st:state) (key:string) (tyargs:list cty) : ML cty =
  match SMap.try_find st.emitted key with
  | Some (DLet d) ->
    let rec zip (ps:list string) (ts:list cty) : list (string & cty) =
      match ps, ts with
      | p :: ps, t :: ts -> (p, t) :: zip ps ts
      | _ -> [] in
    let rec build (bs:list binder) : ML cty =
      match bs with
      | [] -> d.dl_ret
      | [b] -> TArrow (b.b_ty, d.dl_eff, d.dl_ret)
      | b :: bs -> TArrow (b.b_ty, E_Pure, build bs) in
    subst_cty (zip d.dl_typars tyargs) (build d.dl_binders)
  | _ -> TAny

(* Section 3.2: the two ways a call site can fail to be specializable. *)
and split_mono_args (st:state) (l:Ident.lident) (cs:list bclass) (spine:args)
  : ML (list (int & term) & args) =
  if not (has_mono cs) && not (has_dropped cs) then ([], spine)
  else
    let n_args = List.length spine in
    let rec go (i:int) (cs:list bclass) (sp:args) (margs:list (int & term)) (rest:args)
      : ML (list (int & term) & args) =
      match cs, sp with
      | [], _ -> (List.rev margs, List.rev rest @ sp)
      | Poly :: cs, a :: sp -> go (i + 1) cs sp margs (a :: rest)
      (* Section 5.1: an erased argument is deleted, not passed as unit. *)
      | Dropped :: cs, _ :: sp -> go (i + 1) cs sp margs rest
      | Mono :: cs, a :: sp ->
        let t = N.normalize key_norm_steps (tcenv st) (fst a) in
        check_mono_arg st l i t;
        go (i + 1) cs sp ((i, t) :: margs) rest
      | Mono :: _, [] ->
        (* Section 3.2(a): partial application of a specializing definition. *)
        custard_error st E.Error_CustardCannotMonomorphize [
          text ("This use of " ^ Ident.string_of_lid l ^ " supplies only " ^
                show n_args ^ " argument(s), but its binder number " ^ show i ^
                " is monomorphized and so must be given at every call site.");
          text "Eta-expand the use, or drop the [@@monomorphize] attribute."
        ]
      | Poly :: _, []
      | Dropped :: _, [] -> (List.rev margs, List.rev rest)
    in
    go 0 cs spine [] []

(* Section 3.2(b): the argument has to be known at specialization time, i.e. it
   must not mention any of the enclosing definition's runtime parameters.  Note
   the check happens *after* canonicalization, so an argument computed out of
   another [Mono] value (a projection out of a dictionary, say) has already
   been reduced to a closed term and is accepted. *)
and check_mono_arg (st:state) (l:Ident.lident) (i:int) (t:term) : ML unit =
  let free = elems (Free.names t) in
  match free with
  | [] -> ()
  | v :: _ ->
    custard_error st E.Error_CustardCannotMonomorphize [
      text ("The argument passed to the monomorphized binder number " ^ show i ^
            " of " ^ Ident.string_of_lid l ^ " is not known at specialization \
            time: it mentions the runtime parameter " ^
            Ident.string_of_id v.ppname ^ ".");
      text ("Mark " ^ Ident.string_of_id v.ppname ^ " with [@@monomorphize] in \
            the enclosing definition so that it, too, is known at \
            specialization time.")
    ]

(* The effect of a call: we know it exactly, because the callee has already
   been extracted by the time we get here (requests are depth-first). *)
(* A *partially* applied callee is a closure, and building a closure is pure
   however impure calling it will be. *)
and callee_eff (st:state) (key:string) (n_args:int) : ML eff =
  match SMap.try_find st.emitted key with
  | Some (DLet l) ->
    if n_args >= List.length l.dl_binders then l.dl_eff else E_Pure
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
    (* Which subpatterns survive has to be decided exactly as for a
       constructor *application* (see [app_of_fv']), from the constructor's own
       type -- not from the implicit/explicit marks on the subpatterns.  A
       pattern built by a metaprogram (Pulse's elaboration, for one) marks
       nothing implicit, and the two paths disagreeing produces a constructor
       pattern of the wrong arity. *)
    let l = S.lid_of_fv fv in
    let flags = match TcEnv.try_lookup_lid (tcenv st) l with
                | Some ((_, ty), _) -> Mono.erased_binders (tcenv st) ty
                | None -> [] in
    let pats = drop_flagged flags pats |> List.map (fun (p, _) -> pat_of_pat st p) in
    PCtor (request st { sk_lid = l; sk_args = [] }, pats)

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

and extract_lid (st:state) (l:Ident.lident) (nm:name) (margs:list (int & term)) : ML decl =
  let se = TcEnv.lookup_sigelt (tcenv st) l |> Option.map fixup_extract_as in
  (* A rule declared by the definition's own attributes wins over the built-in
     table, so that a program can override a rule it does not like. *)
  let rule = match se with
             | Some se ->
               (match Builtins.rule_of_attributes se.sigattrs with
                | Some r -> Some r
                | None -> Builtins.lookup_rule l)
             | None -> Builtins.lookup_rule l in
  match rule with
  | Some (Builtins.Rule_extern x) ->
    (* Section 8.1, kind 4: the F* "definition" is a specification (often
       literally [admit ()]); the real one lives in a hand-written .ml or .c
       file, and all we owe the backend is the type. *)
    let ty = match TcEnv.try_lookup_lid (tcenv st) l with
             | Some ((_, ty), _) -> ty_of_typ st ty
             | None -> TAny in
    DExternal { dx_name = nm; dx_ty = ty;
                dx_target = x.Builtins.x_name; dx_header = x.Builtins.x_header;
                dx_flags = [] }
  | _ ->
  let is_opaque = (match rule with Some Builtins.Rule_opaque -> true | _ -> false) in
  match se with
  | None ->
    custard_error st E.Error_CustardEntryNotFound [
      text ("Custard cannot find a definition for " ^ Ident.string_of_lid l ^ ".")
    ]
  | Some se ->
    let d = extract_sigelt st l nm margs se in
    let d = if is_opaque then with_no_newtype d else d in
    if is_inlinable se then with_inline d else d

(* [@@FStar.ExtractAs.extract_as impl] replaces a definition's body by [impl]
   for extraction.  This is how Pulse hands us its programs: the F* definition
   of a [fn] is a proof term in Pulse's own syntax, and the attribute carries
   the ordinary [Dv] F* term that it elaborates to.  The ML pipeline does the
   same thing in [FStarC.Extraction.ML.Modul.fixup_sigelt_extract_as]; unlike
   it we do not force the result to be recursive, since Custard's [Rec] flag
   drives the emission order and a spurious cycle would be noise.  Pulse's own
   knot-tying makes the recursive uses visible as ordinary occurrences of [l],
   so testing for them is enough. *)
and fixup_extract_as (se:sigelt) : ML sigelt =
  match se.sigel, List.tryPick ExtractAs.is_extract_as_attr se.sigattrs with
  | Sig_let {lids; lbs=(is_rec, [lb])}, Some impl ->
    let self = match lb.lbname with
               | Inr fv -> mem (S.lid_of_fv fv) (Free.fvars impl)
               | Inl _ -> false in
    { se with sigel = Sig_let {lids; lbs=(is_rec || self, [{lb with lbdef = impl}])} }
  | _ -> se

(* The projectors and discriminators F* derives for an inductive are one field
   read or one tag test each; leaving them as calls would make the output
   unreadable and, in C, slow. *)
and is_inlinable (se:sigelt) : ML bool =
  se.sigquals |> List.existsb (fun q ->
    match q with
    | S.Projector _ | S.Discriminator _ -> true
    | _ -> false)

and with_inline (d:decl) : ML decl =
  match d with
  | DLet l when not (l.dl_flags |> List.existsb Rec?) ->
    DLet { l with dl_flags = Inline :: l.dl_flags }
  | d -> d

(* [@@custard_opaque]: the representation is fixed outside F*, so neither
   erasure nor the newtype collapse of section 5.2 may touch it. *)
and with_no_newtype (d:decl) : ML decl =
  match d with
  | DType t ->
    DType { t with dt_flags = NoNewtype :: List.filter (fun f -> not (Erased? f)) t.dt_flags }
  | d -> d

and extract_sigelt (st:state) (l:Ident.lident) (nm:name) (margs:list (int & term)) (se:sigelt)
  : ML decl =
  match se.sigel with
  | Sig_let {lbs=(is_rec, lbs)} ->
    (match lbs |> List.tryFind (fun lb ->
             match lb.lbname with
             | Inr fv -> Ident.lid_equals (S.lid_of_fv fv) l
             | Inl _ -> false) with
     | Some lb ->
       (* A type abbreviation is a [Sig_let] too; it must not become a value. *)
       if is_type_sig st lb.lbtyp
       then (let d = extract_type_abbrev st nm lb in
             if is_erasable st se || is_prop_sig st lb.lbtyp
             then with_erased_flag d else d)
       else extract_letbinding st l nm lb is_rec margs
     | None -> DExternal { dx_name = nm; dx_ty = TAny; dx_target = None; dx_header = None; dx_flags = [] })

  | Sig_declare_typ {t} ->
    (* An [assume val], or a type whose definition is not available: an
       external symbol, to be realized by the backend or by a custom rule
       (section 8). *)
    if is_type_sig st t
    then DType { dt_name = nm; dt_params = []; dt_body = TAbstract;
                 dt_flags = (if is_erasable st se || is_prop_sig st t
                             then [Erased] else []) }
    else DExternal { dx_name = nm; dx_ty = ty_of_typ st t; dx_target = None; dx_header = None; dx_flags = [] }

  | Sig_inductive_typ {params} ->
    let d = extract_inductive st l nm params in
    if is_erasable st se then with_erased_flag d else d

  | Sig_datacon _ ->
    (* Reached through a constructor application or pattern: what we actually
       want is the type it belongs to, which the layout analysis (M3) will
       need.  For now record it as external so the name exists. *)
    DExternal { dx_name = nm; dx_ty = TAny; dx_target = None; dx_header = None; dx_flags = [] }

  | Sig_bundle {ses} ->
    (match ses |> List.tryFind (fun se ->
             match se.sigel with
             | Sig_inductive_typ {lid} -> Ident.lid_equals lid l
             | _ -> false) with
     | Some se -> extract_sigelt st l nm margs se
     | None -> DType { dt_name = nm; dt_params = []; dt_body = TAbstract; dt_flags = [] })

  | _ ->
    DExternal { dx_name = nm; dx_ty = TAny; dx_target = None; dx_header = None; dx_flags = [] }

(* Section 5.1: a type declared [erasable] has no runtime representation at any
   instantiation, which is what makes it safe to erase uniformly (section
   5.0).  The structural closure -- a type all of whose fields are erased is
   itself erased -- is computed later, by the layout analysis. *)
and is_erasable (st:state) (se:sigelt) : ML bool =
  U.has_attribute se.sigattrs PC.erasable_attr

and with_erased_flag (d:decl) : ML decl =
  match d with
  | DType t -> DType { t with dt_flags = Erased :: t.dt_flags }
  | d -> d

(* [eqtype], [Type0] and friends are all abbreviations, so we have to unfold
   before we can tell a type declaration from a value declaration. *)
and is_type_sig (st:state) (t:typ) : ML bool =
  let _, c = U.arrow_formals_comp t in
  let res = N.normalize [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                         TcEnv.Beta; TcEnv.Iota;
                         TcEnv.UnfoldUntil delta_constant]
                        (tcenv st) (U.comp_result c) in
  (* [eqtype] is a refinement of [Type0], so peel refinements too.  [prop] is
     [assume val prop : Type0], i.e. opaque, so the normalizer cannot reduce it
     to a [Tm_type]; but a [prop]-valued definition such as [eq2] or [l_and] is
     a type constructor all the same. *)
  let rec is_type (t:typ) : ML bool =
    match (SS.compress t).n with
    | Tm_type _ -> true
    | Tm_refine {b} -> is_type b.sort
    | Tm_fvar fv -> S.fv_eq_lid fv PC.prop_lid
    | _ -> false
  in
  is_type res

(* A [prop]-valued type constructor is by definition non-informative, so we can
   tell the layout analysis so directly instead of waiting for the structural
   closure to (fail to) discover it: these are all opaque. *)
and is_prop_sig (st:state) (t:typ) : ML bool =
  let _, c = U.arrow_formals_comp t in
  let res = N.normalize [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                         TcEnv.Beta; TcEnv.Iota;
                         TcEnv.UnfoldUntil delta_constant]
                        (tcenv st) (U.comp_result c) in
  match (SS.compress (U.unrefine res)).n with
  | Tm_fvar fv -> S.fv_eq_lid fv PC.prop_lid
  | _ -> false

and extract_type_abbrev (st:state) (nm:name) (lb:letbinding) : ML decl =
  let bs, body, _ = U.abs_formals lb.lbdef in
  DType {
    dt_name   = nm;
    dt_params = bs |> List.collect (fun b ->
                  if is_type_binder (tcenv st) b then [name_of_bv b.binder_bv] else []);
    dt_body   = TAbbrev (ty_of_typ st body);
    dt_flags  = [];
  }

(* Substitute the [Mono] arguments into the definition and re-abstract over the
   [Poly] ones.  Instead of taking the definition apart we apply it to a
   spine made of the concrete [Mono] arguments and fresh names for the [Poly]
   ones, and let the normalizer do the substitution: that copes uniformly with
   definitions that are eta-short, that have more binders than their type
   shows, or that are not syntactically lambdas at all. *)
and specialize (st:state) (ty:typ) (def:term) (cs:list bclass) (margs:list (int & term))
  : ML (term & comp & list bclass & binders) =
  let bs, c = U.arrow_formals_comp ty in
  let rec go (i:int) (bs:binders) (cs:list bclass) (subst:list subst_elt)
             (spine:args) (poly:binders) (polycs:list bclass)
    : ML (args & binders & list bclass & comp) =
    match bs with
    | [] -> (List.rev spine, List.rev poly, List.rev polycs, SS.subst_comp subst c)
    | b :: bs' ->
      let cls, cs' = match cs with
                     | [] -> Poly, []
                     | c :: cs' -> c, cs' in
      let sort = SS.subst subst b.binder_bv.sort in
      let marg = margs |> List.tryFind (fun (j, _) -> j = i) in
      match cls, marg with
      | Mono, Some (_, a) ->
        go (i + 1) bs' cs' (NT (b.binder_bv, a) :: subst)
           ((a, U.aqual_of_binder b) :: spine) poly polycs
      | _ ->
        (* A [Dropped] binder still has to bind, or the body would have a free
           variable; it is deleted from the emitted signature instead. *)
        let bv = { b.binder_bv with sort = sort } in
        let b' = { b with binder_bv = bv } in
        go (i + 1) bs' cs' subst
           ((S.bv_to_name bv, U.aqual_of_binder b) :: spine) (b' :: poly) (cls :: polycs)
  in
  let spine, poly, polycs, c = go 0 bs cs [] [] [] [] in
  let applied = match spine with [] -> def | _ -> U.mk_app def spine in
  let body = N.normalize custard_norm_steps (tcenv st) applied in
  (U.abs poly body None, c, polycs, poly)

and extract_letbinding (st:state) (l:Ident.lident) (nm:name) (lb:letbinding)
                       (is_rec:bool) (margs:list (int & term)) : ML decl =
  let cs = binder_classes st l in
  let def, c, polycs, poly = specialize st lb.lbtyp lb.lbdef cs margs in
  let bs, body, _ = U.abs_formals def in
  (* [abs_formals] opens the binders under fresh names, but [c] still speaks of
     the ones [specialize] abstracted over.  Left unrelated, the two sets of
     names produce a signature whose result type mentions type variables no
     binder introduces -- fatal in the karamel backend. *)
  let rec realign (ps:binders) (bs:binders) : ML (list subst_elt) =
    match ps, bs with
    | p :: ps, b :: bs -> NT (p.binder_bv, S.bv_to_name b.binder_bv) :: realign ps bs
    | _ -> [] in
  let c = SS.subst_comp (realign poly bs) c in
  (* [U.abs] put the specialized binders first, so [polycs] lines up with the
     head of [bs]; any further binders come from the body's own lambdas and are
     not classified. *)
  let nth_class (i:int) : ML bool =
    let rec go (cs:list bclass) (i:int) : ML bool =
      match cs with
      | [] -> false
      | c :: cs -> if i <= 0 then Dropped? c else go cs (i - 1)
    in
    go polycs i in
  (* Binders past [polycs] come from the body's own lambdas and are filtered by
     the same predicate the call sites use. *)
  let n_poly = List.length polycs in
  let flags = bs |> List.mapi (fun i b ->
                nth_class i || (i >= n_poly && Mono.is_erased_binder (tcenv st) b)) in
  (* [abs_formals] sees through nested lambdas, so a definition written
     [let f x = fun y -> e] has more binders than its type has arrows.  Each
     such extra binder consumes one arrow of the result type -- and its
     effect, which is the one that matters at a call site. *)
  let n_extra =
    flags |> List.mapi (fun i f -> if not f && i >= n_poly then 1 else 0)
          |> List.fold_left (fun a b -> a + b) 0 in
  (* Erased type binders carry no value but do parameterize the signature; the
     karamel backend resolves [TVar]s against this list, so they have to be
     recorded even though they take no runtime argument. *)
  let typars = bs |> List.collect (fun b ->
                 if is_type_binder (tcenv st) b then [name_of_bv b.binder_bv] else []) in
  let bs = drop_flagged flags bs in
  let binders = bs |> List.map (fun b ->
    { b_name = name_of_bv b.binder_bv; b_ty = ty_of_typ st b.binder_bv.sort }) in
  (* The effect is the one of the *codomain*: [lbeff] is the effect of
     evaluating the lambda, which is always Tot. *)
  let rec peel (n:int) (e:eff) (t:cty) : ML (eff & cty) =
    if n <= 0 then (e, t)
    else match t with
         | TArrow (_, e', r) -> peel (n - 1) e' r
         | _ -> (e, t) in
  let eff, ret = peel n_extra (eff_of_comp st c) (ty_of_typ st (U.comp_result c)) in
  DLet {
    dl_name    = nm;
    dl_typars  = typars;
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
  let n_params = List.length params in
  (* Only the *type* parameters become parameters of the target type; a value
     index has no counterpart in the target's type language. *)
  let ty_params = params |> List.collect (fun b ->
                    if is_type_binder (tcenv st) b then [name_of_bv b.binder_bv] else []) in
  let ctor (c:Ident.lident) : ML (name & list (string & cty)) =
    let _, ty = TcEnv.lookup_datacon (tcenv st) c in
    let bs, _ = U.arrow_formals_comp ty in
    (* Drop the inductive's own parameters, which are re-bound by every
       constructor's type under fresh names; the fields' types mention those
       fresh names, so rename them back to the ones the type declaration
       binds. *)
    let bs = if List.length bs >= n_params
             then let pre, bs = List.splitAt n_params bs in
                  let subst = List.map2 (fun (pb:S.binder) (b:S.binder) ->
                                NT (pb.binder_bv, S.bv_to_name b.binder_bv)) pre params in
                  SS.subst_binders subst bs
             else bs in
    (* The remaining binders are the constructor's fields; those without
       runtime content are deleted here, matching what [app_of_fv] does to a
       constructor application. *)
    let bs = drop_flagged (bs |> List.map (Mono.is_erased_binder (tcenv st))) bs in
    (name_of_lid c,
     bs |> List.map (fun b ->
       (name_of_bv b.binder_bv, ty_of_typ st b.binder_bv.sort)))
  in
  DType {
    dt_name   = nm;
    dt_params = ty_params;
    dt_body   = TVariant (ctors |> List.map ctor);
    dt_flags  = [];
  }

(* -------------------------------------------------------------------- *)
(* Driving                                                              *)
(* -------------------------------------------------------------------- *)

let dump_specializations (st:state) : ML unit =
  BU.print_string "Custard specializations:\n";
  SMap.iter st.counts (fun l n ->
    if n > 1 then BU.print2 "  %s -> %s\n" l (show n));
  BU.print1 "  (total: %s)\n" (show (SMap.fold st.counts (fun _ n acc -> acc + n) 0))

let run (st:state) (roots:list Ident.lident) (main:option Ident.lident) : ML program =
  let mark (f:flag) (l:Ident.lident) : ML unit =
    let key = string_of_key { sk_lid = l; sk_args = [] } in
    let _ = request st { sk_lid = l; sk_args = [] } in
    (* Mark the root so backends know which symbols must survive. *)
    match SMap.try_find st.emitted key with
    | Some (DLet d) ->
      SMap.add st.emitted key (DLet { d with dl_flags = f :: d.dl_flags })
    | _ -> () in
  roots |> List.iter (mark Root);
  (match main with Some l -> mark Entrypoint l | None -> ());
  if Options.custard_dump_specializations () then dump_specializations st;
  List.rev !st.order |> List.collect (fun key ->
    match SMap.try_find st.emitted key with
    | Some d -> [d]
    | None -> [])
