(*
   Copyright 2008-2015 Microsoft Research

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
module FStar.Reflection.Basic

open FStar
open FStar.Compiler
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Reflection.Data
open FStar.Syntax.Syntax
open FStar.Order
open FStar.Errors

module S = FStar.Syntax.Syntax // TODO: remove, it's open

module C     = FStar.Const
module PC    = FStar.Parser.Const
module SS    = FStar.Syntax.Subst
module BU    = FStar.Compiler.Util
module Range = FStar.Compiler.Range
module U     = FStar.Syntax.Util
module UF    = FStar.Syntax.Unionfind
module Print = FStar.Syntax.Print
module Ident = FStar.Ident
module Env   = FStar.TypeChecker.Env
module Err   = FStar.Errors
module Z     = FStar.BigInt
module DsEnv = FStar.Syntax.DsEnv
module O     = FStar.Options
module RD    = FStar.Reflection.Data
module EMB   = FStar.Syntax.Embeddings
module N     = FStar.TypeChecker.Normalize
open FStar.VConfig

open FStar.Compiler.Dyn

(* This file provides implementation for reflection primitives in F*.
 *
 * Users can be exposed to (mostly) raw syntax of terms when working in
 * a metaprogramming effect (such as TAC). These effects are irrelevant
 * for runtime and cannot, of course, be used for proof (where syntax
 * inspection would be completely inconsistent
 *)

 (*
  * Most of this file is tedious and repetitive.
  * We should really allow for some metaprogramming in F*. Oh wait....
  *)


(* This is a hack, but it allows to lookup the constructor sigelts when
inspecting a Sig_inductive_typ.

We need to be careful though. If we use this for, say, `lookup_attr` and
remove its `env` argument, then the normalizer can reduce it eagerly.
Trying to do this right now means calls to `lookup_attr` are evaluated
at extraction time, and will not behave as expected. The root cause is
that all of the reflection operators are taken to be pure and that't not
the case if we remove the `env` in some, like `lookup_attr`.

In the case of `inspect_sigelt`, however, I think it won't be
noticeable since one obtain a concrete sigelt without running an impure
metaprogram. *)
let get_env () : Env.env =
  match !N.reflection_env_hook with
  | None -> failwith "impossible: env_hook unset in reflection"
  | Some e -> e

(* private *)
let inspect_bqual (bq : bqual) : aqualv =
    match bq with
    | Some (Implicit _) -> Data.Q_Implicit
    | Some (Meta t) -> Data.Q_Meta t
    | Some Equality
    | None -> Data.Q_Explicit

let inspect_aqual (aq : aqual) : aqualv =
    match aq with
    | Some ({ aqual_implicit = true }) -> Data.Q_Implicit
    | _ -> Data.Q_Explicit

(* private *)
let pack_bqual (aqv : aqualv) : bqual =
    match aqv with
    | Data.Q_Explicit -> None
    | Data.Q_Implicit -> Some (Implicit false)
    | Data.Q_Meta t   -> Some (Meta t)

let pack_aqual (aqv : aqualv) : aqual =
    match aqv with
    | Data.Q_Implicit -> S.as_aqual_implicit true
    | _ -> None
    
let inspect_fv (fv:fv) : list string =
    Ident.path_of_lid (lid_of_fv fv)

let pack_fv (ns:list string) : fv =
    let lid = PC.p2l ns in
    let fallback () =
        let quals =
            (* This an awful hack *)
            if Ident.lid_equals lid PC.cons_lid then Some Data_ctor else
            if Ident.lid_equals lid PC.nil_lid  then Some Data_ctor else
            if Ident.lid_equals lid PC.some_lid then Some Data_ctor else
            if Ident.lid_equals lid PC.none_lid then Some Data_ctor else
            None
        in
        // FIXME: Get a proper delta depth
        lid_as_fv (PC.p2l ns) (Delta_constant_at_level 999) quals
    in
    match !N.reflection_env_hook with
    | None -> fallback ()
    | Some env ->
     let qninfo = Env.lookup_qname env lid in
     match qninfo with
     | Some (Inr (se, _us), _rng) ->
         let quals = DsEnv.fv_qual_of_se se in
         // FIXME: Get a proper delta depth
         lid_as_fv (PC.p2l ns) (Delta_constant_at_level 999) quals
     | _ ->
         fallback ()

// TODO: move to library?
let rec last (l:list 'a) : 'a =
    match l with
    | [] -> failwith "last: empty list"
    | [x] -> x
    | _::xs -> last xs

let rec init (l:list 'a) : list 'a =
    match l with
    | [] -> failwith "init: empty list"
    | [x] -> []
    | x::xs -> x :: init xs

let inspect_const (c:sconst) : vconst =
    match c with
    | FStar.Const.Const_unit -> C_Unit
    | FStar.Const.Const_int (s, _) -> C_Int (Z.big_int_of_string s)
    | FStar.Const.Const_bool true  -> C_True
    | FStar.Const.Const_bool false -> C_False
    | FStar.Const.Const_string (s, _) -> C_String s
    | FStar.Const.Const_range r -> C_Range r
    | FStar.Const.Const_reify _ -> C_Reify
    | FStar.Const.Const_reflect l -> C_Reflect (Ident.path_of_lid l)
    | _ -> failwith (BU.format1 "unknown constant: %s" (Print.const_to_string c))

let inspect_universe u =
  match u with
  | U_zero -> Uv_Zero
  | U_succ u -> Uv_Succ u
  | U_max us -> Uv_Max us
  | U_bvar n -> Uv_BVar (Z.of_int_fs n)
  | U_name i -> Uv_Name (Ident.string_of_id i, Ident.range_of_id i)
  | U_unif u -> Uv_Unif u
  | U_unknown -> Uv_Unk

let pack_universe uv =
  match uv with
  | Uv_Zero -> U_zero
  | Uv_Succ u -> U_succ u
  | Uv_Max us -> U_max us
  | Uv_BVar n -> U_bvar (Z.to_int_fs n)
  | Uv_Name i -> U_name (Ident.mk_ident i)
  | Uv_Unif u -> U_unif u
  | Uv_Unk -> U_unknown

let rec inspect_ln (t:term) : term_view =
    //
    // Only pushes delayed substitutions,
    //   doesn't compress uvars
    //
    let t = t |> SS.compress_subst in
    match t.n with
    | Tm_meta (t, _) ->
        inspect_ln t

    | Tm_name bv ->
        Tv_Var bv

    | Tm_bvar bv ->
        Tv_BVar bv

    | Tm_fvar fv ->
        Tv_FVar fv

    | Tm_uinst (t, us) ->
      (match t.n with
       | Tm_fvar fv -> Tv_UInst (fv, us)
       | _ -> failwith "Reflection::inspect_ln: uinst for a non-fvar node")

    | Tm_ascribed (t, (Inl ty, tacopt, eq), _elid) ->
        Tv_AscribedT (t, ty, tacopt, eq)

    | Tm_ascribed (t, (Inr cty, tacopt, eq), elid) ->
        Tv_AscribedC (t, cty, tacopt, eq)

    | Tm_app (hd, []) ->
        failwith "inspect_ln: empty arguments on Tm_app"

    | Tm_app (hd, args) ->
        // We split at the last argument, since the term_view does not
        // expose n-ary lambdas buy unary ones.
        let (a, q) = last args in
        let q' = inspect_aqual q in
        Tv_App (U.mk_app hd (init args), (a, q'))

    | Tm_abs ([], _, _) ->
        failwith "inspect_ln: empty arguments on Tm_abs"

    | Tm_abs (b::bs, t, k) ->
        let body =
            match bs with
            | [] -> t
            | bs -> S.mk (Tm_abs (bs, t, k)) t.pos
        in
        Tv_Abs (b, body)

    | Tm_type u ->
        Tv_Type u

    | Tm_arrow ([], k) ->
        failwith "inspect_ln: empty binders on arrow"

    | Tm_arrow _ ->
        begin match U.arrow_one_ln t with
        | Some (b, c) -> Tv_Arrow (b, c)
        | None -> failwith "impossible"
        end

    | Tm_refine (bv, t) ->
        Tv_Refine (bv, t)

    | Tm_constant c ->
        Tv_Const (inspect_const c)

    | Tm_uvar (ctx_u, s) ->
        //
        // Use the unique id of the uvar
        //
        Tv_Uvar (Z.of_int_fs (UF.uvar_unique_id ctx_u.ctx_uvar_head),
                (ctx_u, s))

    | Tm_let ((false, [lb]), t2) ->
        if lb.lbunivs <> [] then Tv_Unknown else
        begin match lb.lbname with
        | Inr _ -> Tv_Unknown // no top level lets
        | Inl bv ->
            // The type of `bv` should match `lb.lbtyp`
            Tv_Let (false, lb.lbattrs, bv, lb.lbdef, t2)
        end

    | Tm_let ((true, [lb]), t2) ->
        if lb.lbunivs <> [] then Tv_Unknown else
        begin match lb.lbname with
        | Inr _  -> Tv_Unknown // no top level lets
        | Inl bv -> Tv_Let (true, lb.lbattrs, bv, lb.lbdef, t2)
        end

    | Tm_match (t, ret_opt, brs, _) ->
        let rec inspect_pat p =
            match p.v with
            | Pat_constant c -> Pat_Constant (inspect_const c)
            | Pat_cons (fv, us_opt, ps) -> Pat_Cons (fv, us_opt, List.map (fun (p, b) -> inspect_pat p, b) ps)
            | Pat_var bv -> Pat_Var bv
            | Pat_wild bv -> Pat_Wild bv
            | Pat_dot_term eopt -> Pat_Dot_Term eopt
        in
        let brs = List.map (function (pat, _, t) -> (inspect_pat pat, t)) brs in
        Tv_Match (t, ret_opt, brs)

    | Tm_unknown ->
        Tv_Unknown

    | Tm_lazy i ->
        // Not calling U.unlazy_emb since that calls (stateful) SS.compress
        i |> U.unfold_lazy |> inspect_ln

    | _ ->
        Err.log_issue t.pos (Err.Warning_CantInspect, BU.format2 "inspect_ln: outside of expected syntax (%s, %s)" (Print.tag_of_term t) (Print.term_to_string t));
        Tv_Unknown

let inspect_comp (c : comp) : comp_view =
    let get_dec (flags : list cflag) : list term =
        match List.tryFind (function DECREASES _ -> true | _ -> false) flags with
        | None -> []
        | Some (DECREASES (Decreases_lex ts)) -> ts
        | Some (DECREASES (Decreases_wf _)) ->
          Err.log_issue c.pos (Err.Warning_CantInspect,
            BU.format1 "inspect_comp: inspecting comp with wf decreases clause is not yet supported: %s \
              skipping the decreases clause"
              (Print.comp_to_string c));
          []
        | _ -> failwith "Impossible!"
    in
    match c.n with
    | Total t -> C_Total t
    | GTotal t -> C_GTotal t
    | Comp ct -> begin
        let uopt =
          if List.length ct.comp_univs = 0
          then U_unknown
          else ct.comp_univs |> List.hd in
        if Ident.lid_equals ct.effect_name PC.effect_Lemma_lid then
            match ct.effect_args with
            | (pre,_)::(post,_)::(pats,_)::_ ->
                C_Lemma (pre, post, pats)
            | _ ->
                failwith "inspect_comp: Lemma does not have enough arguments?"
        else
            let inspect_arg (a, q) = (a, inspect_aqual q) in
            C_Eff (ct.comp_univs,
                   Ident.path_of_lid ct.effect_name,
                   ct.result_typ,
                   List.map inspect_arg ct.effect_args,
                   get_dec ct.flags)
      end

let pack_comp (cv : comp_view) : comp =
    let urefl_to_univs u =
      if u = U_unknown
      then []
      else [u] in
    let urefl_to_univ_opt u =
      if u = U_unknown
      then None
      else Some u in
    match cv with
    | C_Total t -> mk_Total t
    | C_GTotal t -> mk_GTotal t
    | C_Lemma (pre, post, pats) ->
        let ct = { comp_univs  = []
                 ; effect_name = PC.effect_Lemma_lid
                 ; result_typ  = S.t_unit
                 ; effect_args = [S.as_arg pre; S.as_arg post; S.as_arg pats]
                 ; flags       = [] } in
        S.mk_Comp ct

    | C_Eff (us, ef, res, args, decrs) ->
        let pack_arg (a, q) = (a, pack_aqual q) in
        let flags =
          if List.length decrs = 0
          then []
          else [DECREASES (Decreases_lex decrs)] in
        let ct = { comp_univs  = us
                 ; effect_name = Ident.lid_of_path ef Range.dummyRange
                 ; result_typ  = res
                 ; effect_args = List.map pack_arg args
                 ; flags       = flags } in
        S.mk_Comp ct

let pack_const (c:vconst) : sconst =
    match c with
    | C_Unit         -> C.Const_unit
    | C_Int i        -> C.Const_int (Z.string_of_big_int i, None)
    | C_True         -> C.Const_bool true
    | C_False        -> C.Const_bool false
    | C_String s     -> C.Const_string (s, Range.dummyRange)
    | C_Range  r     -> C.Const_range r
    | C_Reify        -> C.Const_reify None
    | C_Reflect ns   -> C.Const_reflect (Ident.lid_of_path ns Range.dummyRange)

// TODO: pass in range?
let pack_ln (tv:term_view) : term =
    match tv with
    | Tv_Var bv ->
        S.bv_to_name bv

    | Tv_BVar bv ->
        S.bv_to_tm bv

    | Tv_FVar fv ->
        S.fv_to_tm fv

    | Tv_UInst (fv, us) ->
      mk_Tm_uinst (S.fv_to_tm fv) us

    | Tv_App (l, (r, q)) ->
        let q' = pack_aqual q in
        U.mk_app l [(r, q')]

    | Tv_Abs (b, t) ->
        mk (Tm_abs ([b], t, None)) t.pos // TODO: effect?

    | Tv_Arrow (b, c) ->
        mk (Tm_arrow ([b], c)) c.pos

    | Tv_Type u ->
        mk (Tm_type u) Range.dummyRange

    | Tv_Refine (bv, t) ->
        mk (Tm_refine (bv, t)) t.pos

    | Tv_Const c ->
        S.mk (Tm_constant (pack_const c)) Range.dummyRange

    | Tv_Uvar (u, ctx_u_s) ->
      S.mk (Tm_uvar ctx_u_s) Range.dummyRange

    | Tv_Let (false, attrs, bv, t1, t2) ->
        let lb = U.mk_letbinding (Inl bv) [] bv.sort PC.effect_Tot_lid t1 attrs Range.dummyRange in
        S.mk (Tm_let ((false, [lb]), t2)) Range.dummyRange

    | Tv_Let (true, attrs, bv, t1, t2) ->
        let lb = U.mk_letbinding (Inl bv) [] bv.sort PC.effect_Tot_lid t1 attrs Range.dummyRange in
        S.mk (Tm_let ((true, [lb]), t2)) Range.dummyRange

    | Tv_Match (t, ret_opt, brs) ->
        let wrap v = {v=v;p=Range.dummyRange} in
        let rec pack_pat p : S.pat =
            match p with
            | Pat_Constant c -> wrap <| Pat_constant (pack_const c)
            | Pat_Cons (fv, us_opt, ps) -> wrap <| Pat_cons (fv, us_opt, List.map (fun (p, b) -> pack_pat p, b) ps)
            | Pat_Var  bv -> wrap <| Pat_var bv
            | Pat_Wild bv -> wrap <| Pat_wild bv
            | Pat_Dot_Term eopt -> wrap <| Pat_dot_term eopt
        in
        let brs = List.map (function (pat, t) -> (pack_pat pat, None, t)) brs in
        S.mk (Tm_match (t, ret_opt, brs, None)) Range.dummyRange

    | Tv_AscribedT(e, t, tacopt, use_eq) ->
        S.mk (Tm_ascribed(e, (Inl t, tacopt, use_eq), None)) Range.dummyRange

    | Tv_AscribedC(e, c, tacopt, use_eq) ->
        S.mk (Tm_ascribed(e, (Inr c, tacopt, use_eq), None)) Range.dummyRange

    | Tv_Unknown ->
        S.mk Tm_unknown Range.dummyRange

let compare_bv (x:bv) (y:bv) : order =
    let n = S.order_bv x y in
    if n < 0 then Lt
    else if n = 0 then Eq
    else Gt

let lookup_attr (attr:term) (env:Env.env) : list fv =
    match (SS.compress_subst attr).n with
    | Tm_fvar fv ->
        let ses = Env.lookup_attr env (Ident.string_of_lid (lid_of_fv fv)) in
        List.concatMap (fun se -> match U.lid_of_sigelt se with
                                  | None -> []
                                  // FIXME: Get a proper delta depth
                                  | Some l -> [S.lid_as_fv l (S.Delta_constant_at_level 999) None]) ses
    | _ -> []

let all_defs_in_env (env:Env.env) : list fv =
    List.map (fun l -> S.lid_as_fv l (S.Delta_constant_at_level 999) None) (Env.lidents env) // |> take 10

let defs_in_module (env:Env.env) (modul:name) : list fv =
    List.concatMap
        (fun l ->
                (* must succeed, ids_of_lid always returns a non-empty list *)
                let ns = Ident.ids_of_lid l |> init |> List.map Ident.string_of_id in
                if ns = modul
                then [S.lid_as_fv l (S.Delta_constant_at_level 999) None]
                else [])
        (Env.lidents env)

let lookup_typ (env:Env.env) (ns:list string) : option sigelt =
    let lid = PC.p2l ns in
    Env.lookup_sigelt env lid

let sigelt_attrs (se : sigelt) : list attribute =
    se.sigattrs

let set_sigelt_attrs (attrs : list attribute) (se : sigelt) : sigelt =
    { se with sigattrs = attrs }

(* PRIVATE, and hacky :-( *)
let rd_to_syntax_qual : RD.qualifier -> qualifier = function
  | RD.Assumption -> Assumption
  | RD.New -> New
  | RD.Private -> Private
  | RD.Unfold_for_unification_and_vcgen -> Unfold_for_unification_and_vcgen
  | RD.Visible_default -> Visible_default
  | RD.Irreducible -> Irreducible
  | RD.Inline_for_extraction -> Inline_for_extraction
  | RD.NoExtract -> NoExtract
  | RD.Noeq -> Noeq
  | RD.Unopteq -> Unopteq
  | RD.TotalEffect -> TotalEffect
  | RD.Logic -> Logic
  | RD.Reifiable -> Reifiable
  | RD.Reflectable l -> Reflectable l
  | RD.Discriminator l -> Discriminator l
  | RD.Projector (l, i) -> Projector (l, i)
  | RD.RecordType (l1, l2) -> RecordType (l1, l2)
  | RD.RecordConstructor (l1, l2) -> RecordConstructor (l1, l2)
  | RD.Action l -> Action l
  | RD.ExceptionConstructor -> ExceptionConstructor
  | RD.HasMaskedEffect -> HasMaskedEffect
  | RD.Effect -> S.Effect
  | RD.OnlyName -> OnlyName

let syntax_to_rd_qual = function
  | Assumption -> RD.Assumption
  | New -> RD.New
  | Private -> RD.Private
  | Unfold_for_unification_and_vcgen -> RD.Unfold_for_unification_and_vcgen
  | Visible_default -> RD.Visible_default
  | Irreducible -> RD.Irreducible
  | Inline_for_extraction -> RD.Inline_for_extraction
  | NoExtract -> RD.NoExtract
  | Noeq -> RD.Noeq
  | Unopteq -> RD.Unopteq
  | TotalEffect -> RD.TotalEffect
  | Logic -> RD.Logic
  | Reifiable -> RD.Reifiable
  | Reflectable l -> RD.Reflectable l
  | Discriminator l -> RD.Discriminator l
  | Projector (l, i) -> RD.Projector (l, i)
  | RecordType (l1, l2) -> RD.RecordType (l1, l2)
  | RecordConstructor (l1, l2) -> RD.RecordConstructor (l1, l2)
  | Action l -> RD.Action l
  | ExceptionConstructor -> RD.ExceptionConstructor
  | HasMaskedEffect -> RD.HasMaskedEffect
  | S.Effect -> RD.Effect
  | OnlyName -> RD.OnlyName


let sigelt_quals (se : sigelt) : list RD.qualifier =
    se.sigquals |> List.map syntax_to_rd_qual

let set_sigelt_quals (quals : list RD.qualifier) (se : sigelt) : sigelt =
    { se with sigquals = List.map rd_to_syntax_qual quals }

let sigelt_opts (se : sigelt) : option vconfig = se.sigopts

let embed_vconfig (vcfg : vconfig) : term =
  EMB.embed EMB.e_vconfig vcfg Range.dummyRange None EMB.id_norm_cb

let inspect_sigelt (se : sigelt) : sigelt_view =
    match se.sigel with
    | Sig_let ((r, lbs), _) ->
        let inspect_letbinding (lb:letbinding) =
            let {lbname=nm;lbunivs=us;lbtyp=typ;lbeff=eff;lbdef=def;lbattrs=attrs;lbpos=pos} = lb in
            let s, us = SS.univ_var_opening us in
            let typ = SS.subst s typ in
            let def = SS.subst s def in
            U.mk_letbinding nm us typ eff def attrs pos
        in
        Sg_Let (r, List.map inspect_letbinding lbs)

    | Sig_inductive_typ (lid, us, param_bs, _num_uniform, ty, _mutual, c_lids) ->
        let nm = Ident.path_of_lid lid in
        let s, us = SS.univ_var_opening us in
        let param_bs = SS.subst_binders s param_bs in
        let ty = SS.subst s ty in

        let param_bs, ty = SS.open_term param_bs ty in

        let inspect_ctor (c_lid:Ident.lid) : ctor =
          match Env.lookup_sigelt (get_env ()) c_lid with
          | Some ({sigel = Sig_datacon (lid, us, cty, _ty_lid_, nparam, _mutual)}) ->
            let cty = SS.subst s cty in // open universes from above

            let param_ctor_bs, c = N.get_n_binders (get_env ()) nparam cty in

            if List.length param_ctor_bs <> nparam then
              failwith "impossible: inspect_sigelt: could not obtain sufficient ctor param binders";

            if not (U.is_total_comp c) then
              failwith "impossible: inspect_sigelt: removed parameters and got an effectful comp";
            let cty = U.comp_result c in

            (* Substitute the parameters of the constructor to match
             * those of the inductive opened above, and return the type
             * of the constructor already instantiated. *)
            let s' = List.map2 (fun b1 b2 -> NT (b1.binder_bv, S.bv_to_name b2.binder_bv))
                               param_ctor_bs param_bs
            in
            let cty = SS.subst s' cty in

            let cty = U.remove_inacc cty in
            (Ident.path_of_lid lid, cty)

          | _ ->
            failwith "impossible: inspect_sigelt: did not find ctor"
        in
        Sg_Inductive (nm, us, param_bs, ty, List.map inspect_ctor c_lids)

    | Sig_declare_typ (lid, us, ty) ->
        let nm = Ident.path_of_lid lid in
        let us, ty = SS.open_univ_vars us ty in
        Sg_Val (nm, us, ty)

    | _ ->
        Unk

let pack_sigelt (sv:sigelt_view) : sigelt =
    let check_lid lid =
        if List.length (Ident.path_of_lid lid) <= 1
	then failwith ("pack_sigelt: invalid long identifier \""
	              ^ Ident.string_of_lid lid
		      ^ "\" (did you forget a module path?)")
    in
    match sv with
    | Sg_Let (r, lbs) ->
        let pack_letbinding (lb:letbinding) =
	    let {lbname=nm;lbunivs=us;lbtyp=typ;lbeff=eff;lbdef=def;lbattrs=attrs;lbpos=pos} = lb in
            let lid = match nm with
                      | Inr fv -> lid_of_fv fv
                      | _ -> failwith
                              "impossible: pack_sigelt: bv in toplevel let binding"
            in
            check_lid lid;
            let s = SS.univ_var_closing us in
            let typ = SS.subst s typ in
            let def = SS.subst s def in
            let lb = U.mk_letbinding nm us typ eff def attrs pos in
            (lid, lb)
        in
	let packed = List.map pack_letbinding lbs in
	let lbs = List.map snd packed in
	let lids = List.map fst packed in
        mk_sigelt <| Sig_let ((r, lbs), lids)

    | Sg_Inductive (nm, us_names, param_bs, ty, ctors) ->
      let ind_lid = Ident.lid_of_path nm Range.dummyRange in
      check_lid ind_lid;
      let s = SS.univ_var_closing us_names in
      let nparam = List.length param_bs in
      let pack_ctor (c:ctor) : sigelt =
        let (nm, ty) = c in
        let lid = Ident.lid_of_path nm Range.dummyRange in
        let ty = U.arrow param_bs (S.mk_Total ty) in
        let ty = SS.subst s ty in (* close univs *)
        mk_sigelt <| Sig_datacon (lid, us_names, ty, ind_lid, nparam, [])
      in

      let ctor_ses : list sigelt = List.map pack_ctor ctors in
      let c_lids : list Ident.lid = List.map (fun se -> BU.must (U.lid_of_sigelt se)) ctor_ses in

      let ind_se : sigelt =
        let param_bs = SS.close_binders param_bs in
        let ty = SS.close param_bs ty in

        (* close univs *)
        let param_bs = SS.subst_binders s param_bs in
        let ty = SS.subst s ty in
        //We can't trust the assignment of num uniform binders from the reflection API
        //So, set it to None; it has to be checked and recomputed
        mk_sigelt <| Sig_inductive_typ (ind_lid, us_names, param_bs, None, ty, [], c_lids)
      in
      let se = mk_sigelt <| Sig_bundle (ind_se::ctor_ses, ind_lid::c_lids) in
      { se with sigquals = Noeq::se.sigquals }

    | Sg_Val (nm, us_names, ty) ->
        let val_lid = Ident.lid_of_path nm Range.dummyRange in
        check_lid val_lid;
        let typ = SS.close_univ_vars us_names ty in
        mk_sigelt <| Sig_declare_typ (val_lid, us_names, typ)

    | Unk ->
        failwith "packing Unk, sorry"

let inspect_lb (lb:letbinding) : lb_view =
    let {lbname=nm;lbunivs=us;lbtyp=typ;lbeff=eff;lbdef=def;lbattrs=attrs;lbpos=pos}
        = lb in
    let s, us = SS.univ_var_opening us in
    let typ = SS.subst s typ in
    let def = SS.subst s def in
    match nm with
    | Inr fv -> {lb_fv = fv; lb_us = us; lb_typ = typ; lb_def = def}
    | _ -> failwith "Impossible: bv in top-level let binding"

let pack_lb (lbv:lb_view) : letbinding =
    let {lb_fv = fv; lb_us = us; lb_typ = typ; lb_def = def} = lbv in
    let s = SS.univ_var_closing us in
    let typ = SS.subst s typ in
    let def = SS.subst s def in
    U.mk_letbinding (Inr fv) us typ PC.effect_Tot_lid def [] Range.dummyRange

let inspect_bv (bv:bv) : bv_view =
    if bv.index < 0 then (
        Err.log_issue Range.dummyRange
            (Err.Warning_CantInspect, BU.format3 "inspect_bv: index is negative (%s : %s), index = %s"
                                         (Ident.string_of_id bv.ppname)
                                         (Print.term_to_string bv.sort)
                                         (string_of_int bv.index))
    );
    {
      bv_ppname = Ident.string_of_id bv.ppname;
      bv_index = Z.of_int_fs bv.index;
      bv_sort = bv.sort;
    }

let pack_bv (bvv:bv_view) : bv =
    if Z.to_int_fs bvv.bv_index < 0 then (
        Err.log_issue Range.dummyRange
            (Err.Warning_CantInspect, BU.format3 "pack_bv: index is negative (%s : %s), index = %s"
                                         bvv.bv_ppname
                                         (Print.term_to_string bvv.bv_sort)
                                         (string_of_int (Z.to_int_fs bvv.bv_index)))
    );
    {
      ppname = Ident.mk_ident (bvv.bv_ppname, Range.dummyRange);
      index = Z.to_int_fs bvv.bv_index; // Guaranteed to be a nat
      sort = bvv.bv_sort;
    }

let inspect_binder (b:binder) : binder_view = 
  let attrs = U.encode_positivity_attributes b.binder_positivity b.binder_attrs in
  {
    binder_bv = b.binder_bv;
    binder_qual = inspect_bqual (b.binder_qual);
    binder_attrs = attrs
  }

let pack_binder (bview:binder_view) : binder = 
  let pqual, attrs = U.parse_positivity_attributes bview.binder_attrs in
  {
    binder_bv=bview.binder_bv;
    binder_qual=pack_bqual (bview.binder_qual);
    binder_positivity=pqual;
    binder_attrs=attrs
  }

open FStar.TypeChecker.Env
let moduleof (e : Env.env) : list string =
    Ident.path_of_lid e.curmodule

let env_open_modules (e : Env.env) : list name =
    List.map (fun (l, m) -> List.map Ident.string_of_id (Ident.ids_of_lid l))
             (DsEnv.open_modules e.dsenv)

let binders_of_env e = FStar.TypeChecker.Env.all_binders e

(* Generic combinators, safe *)
let eqopt  = Syntax.Util.eqopt
let eqlist = Syntax.Util.eqlist
let eqprod = Syntax.Util.eqprod

(*
 * Why doesn't this call into Syntax.Util.term_eq? Because that function
 * can expose details that are not observable in the userspace view of
 * terms, and hence that function cannot be safely exposed if we wish to
 * maintain the lemmas stating that pack/inspect are inverses of each
 * other.
 *
 * In other words, we need this function to be implemented consistently
 * with the view to make sure it is a _function_ in userspace, and maps
 * (propositionally) equal terms to equal results.
 *
 * So we implement it via inspect_ln, to make sure we don't reveal
 * anything inspect_ln does not already reveal. Hence this function
 * is really only an optimization of this same implementation done in
 * userspace. Also, nothing is guaranted about its result. It if were to
 * just return false constantly, that would be safe (though useless).
 *
 * This same note also applies to comp, and other types that are taken
 * as abstract, but have a lemma stating that the view is complete
 * (or appear inside a view of one such type).
 *)
let rec term_eq (t1:term) (t2:term) : bool =
  match inspect_ln t1, inspect_ln t2 with
  | Tv_Var bv1, Tv_Var bv2 ->
    bv_eq bv1 bv2

  | Tv_BVar bv1, Tv_BVar bv2 ->
    bv_eq bv1 bv2

  | Tv_FVar fv1, Tv_FVar fv2 ->
    (* This should be equivalent to exploding the fv's name comparing *)
    S.fv_eq fv1 fv2

  | Tv_UInst (fv1, us1), Tv_UInst (fv2, us2) ->
    S.fv_eq fv1 fv2 && univs_eq us1 us2

  | Tv_App (h1, arg1), Tv_App (h2, arg2) ->
    term_eq h1 h2 && arg_eq arg1 arg2

  | Tv_Abs (b1, t1), Tv_Abs (b2, t2) ->
    binder_eq b1 b2 && term_eq t1 t2

  | Tv_Arrow (b1, c1), Tv_Arrow (b2, c2) ->
    binder_eq b1 b2 && comp_eq c1 c2

  | Tv_Type u1, Tv_Type u2 ->
    univ_eq u1 u2

  | Tv_Refine (b1, t1), Tv_Refine (b2, t2) ->
    term_eq b1.sort b2.sort && term_eq t1 t2

  | Tv_Const c1, Tv_Const c2 ->
    const_eq c1 c2

  | Tv_Uvar (n1, uv1), Tv_Uvar (n2, uv2) ->
    (*
     * The uvs are completely opaque in userspace, so we could do a fancier
     * check here without compromising soundness. But.. we cannot really check
     * the unionfind graph, I think, since the result could differ as things get
     * unified (though it's unclear if that can happen within two calls to this
     * function within a *single* definition.. since uvars do not survive across
     * top-levels.
     *
     * Anyway, for now just compare the associated ints. Which are *definitely*
     * visible by users.
     *)
    n1 = n2

  | Tv_Let (r1, ats1, bv1, m1, n1), Tv_Let (r2, ats2, bv2, m2, n2) ->
    r1 = r2 &&
     eqlist term_eq ats1 ats2 &&
     term_eq bv1.sort bv2.sort &&
     term_eq m1 m2 &&
     term_eq n1 n2

  | Tv_Match (h1, an1, brs1), Tv_Match (h2, an2, brs2) ->
    term_eq h1 h2 &&
      eqopt match_ret_asc_eq an1 an2 &&
      eqlist branch_eq brs1 brs2

  | Tv_AscribedT (e1, t1, topt1, eq1), Tv_AscribedT (e2, t2, topt2, eq2) ->
    term_eq e1 e2 &&
      term_eq t1 t2 &&
      eqopt term_eq topt1 topt2 &&
      eq1 = eq2

  | Tv_AscribedC (e1, c1, topt1, eq1), Tv_AscribedC (e2, c2, topt2, eq2) ->
    term_eq e1 e2 &&
      comp_eq c1 c2 &&
      eqopt term_eq topt1 topt2 &&
      eq1 = eq2

  | Tv_Unknown, Tv_Unknown -> true
  | _ -> false

and arg_eq (arg1 : argv) (arg2 : argv) : bool =
  let (a1, aq1) = arg1 in
  let (a2, aq2) = arg2 in
  term_eq a1 a2 && aqual_eq aq1 aq2

and aqual_eq (aq1 : aqualv) (aq2 : aqualv) : bool =
  match aq1, aq2 with
  | Q_Implicit, Q_Implicit -> true
  | Q_Explicit, Q_Explicit -> true
  | Q_Meta t1, Q_Meta t2 -> term_eq t1 t2
  | _ -> false

and binder_eq (b1 : binder) (b2 : binder) : bool =
  let bview1 = inspect_binder b1 in
  let bview2 = inspect_binder b2 in
  binding_bv_eq bview1.binder_bv bview2.binder_bv &&
    aqual_eq bview1.binder_qual bview2.binder_qual &&
    eqlist term_eq bview1.binder_attrs bview2.binder_attrs

and binding_bv_eq (bv1 : bv) (bv2 : bv) : bool =
  (*
   * In binding ocurrences, we compare the sorts of variables. Not so
   * in normal ocurrences, as term_eq does. Note we can access the sort
   * safely since it's exactly what inspect_bv does.
   *
   * We do _not_ compare the indices. This is a binding ocurrence, so
   * they do not matter at all.
   *)
  term_eq bv1.sort bv2.sort

and bv_eq (bv1 : bv) (bv2 : bv) : bool =
  (*
   * Just compare the index. Note: this is safe since inspect_bv
   * exposes it. We do _not_ compare the sorts. This is already
   * what Syntax.Util.term_eq does, and they arguably should not
   * be there.
   *)
  bv1.index = bv2.index

and comp_eq (c1 : comp) (c2 : comp) : bool =
  match inspect_comp c1, inspect_comp c2 with
  | C_Total t1, C_Total t2
  | C_GTotal t1, C_GTotal t2 ->
    term_eq t1 t2

  | C_Lemma (pre1, post1, pats1), C_Lemma (pre2, post2, pats2) ->
    term_eq pre1 pre2 && term_eq post1 post2 && term_eq pats1 pats2

  | C_Eff (us1, name1, t1, args1, decrs1), C_Eff (us2, name2, t2, args2, decrs2) ->
    univs_eq us1 us2 &&
    name1 = name2 &&
    term_eq t1 t2 &&
    eqlist arg_eq args1 args2 &&
    eqlist term_eq decrs1 decrs2

  | _ ->
    false

and match_ret_asc_eq (a1 : match_returns_ascription) (a2 : match_returns_ascription) : bool =
  eqprod binder_eq ascription_eq a1 a2

and ascription_eq (asc1 : ascription) (asc2 : ascription) : bool =
  let (a1, topt1, eq1) = asc1 in
  let (a2, topt2, eq2) = asc2 in
  (match a1, a2 with
   | Inl t1, Inl t2 -> term_eq t1 t2
   | Inr c1, Inr c2 -> comp_eq c1 c2) &&
     eqopt term_eq topt1 topt2 &&
     eq1 = eq2

and branch_eq (c1 : Data.branch) (c2 : Data.branch) : bool =
  eqprod pattern_eq term_eq c1 c2

and pattern_eq (p1 : pattern) (p2 : pattern) : bool =
  match p1, p2 with
  | Pat_Constant c1, Pat_Constant c2 ->
    const_eq c1 c2
  | Pat_Cons (fv1, us1, subpats1), Pat_Cons (fv2, us2, subpats2) ->
    S.fv_eq fv1 fv2 &&
      eqopt (eqlist univ_eq) us1 us2 &&
      eqlist (eqprod pattern_eq (fun b1 b2 -> b1 = b2)) subpats1 subpats2

  | Pat_Var bv1, Pat_Var bv2 ->
    binding_bv_eq bv1 bv2

  | Pat_Wild bv1, Pat_Wild bv2 ->
    binding_bv_eq bv1 bv2

  | Pat_Dot_Term topt1, Pat_Dot_Term topt2 ->
    eqopt term_eq topt1 topt2

  | _ -> false

and const_eq (c1 : vconst) (c2 : vconst) : bool =
  c1 = c2

and univ_eq (u1 : universe) (u2 : universe) : bool =
  Syntax.Util.eq_univs u1 u2 // FIXME!

and univs_eq (us1 : list universe) (us2 : list universe) : bool =
  eqlist univ_eq us1 us2

let implode_qn ns = String.concat "." ns
let explode_qn s = String.split ['.'] s
let compare_string s1 s2 = Z.of_int_fs (String.compare s1 s2)

let push_binder e b = Env.push_binders e [b]

let subst (x:bv) (n:term) (m:term) : term =
  SS.subst [NT(x,n)] m

let close_term (b:binder) (t:term) : term = SS.close [b] t
