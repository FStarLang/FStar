#light "off"
module FStar.Reflection.Basic

open FStar
open FStar.All
open FStar.Reflection.Data
open FStar.Syntax.Syntax
open FStar.Order
open FStar.Errors

module S = FStar.Syntax.Syntax // TODO: remove, it's open

module C     = FStar.Const
module PC    = FStar.Parser.Const
module SS    = FStar.Syntax.Subst
module BU    = FStar.Util
module Range = FStar.Range
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

open FStar.Dyn

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
//TODO: AR: inspect for attributes code is missing
let inspect_aqual (aq : aqual) : aqualv =
    match aq with
    | Some (Implicit _) -> Data.Q_Implicit
    | Some (Meta t) -> Data.Q_Meta t
    | Some Equality
    | None -> Data.Q_Explicit

(* private *)
let pack_aqual (aqv : aqualv) : aqual =
    match aqv with
    | Data.Q_Explicit -> None
    | Data.Q_Implicit -> Some (Implicit false)
    | Data.Q_Meta t   -> Some (Meta t)
    | Data.Q_Meta_attr t   -> None //TODO: AR: FIXME: Some (Meta (Arg_qualifier_meta_attr t))

let inspect_fv (fv:fv) : list<string> =
    Ident.path_of_lid (lid_of_fv fv)

let pack_fv (ns:list<string>) : fv =
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
     | Some (BU.Inr (se, _us), _rng) ->
         let quals = DsEnv.fv_qual_of_se se in
         // FIXME: Get a proper delta depth
         lid_as_fv (PC.p2l ns) (Delta_constant_at_level 999) quals
     | _ ->
         fallback ()

// TODO: move to library?
let rec last (l:list<'a>) : 'a =
    match l with
    | [] -> failwith "last: empty list"
    | [x] -> x
    | _::xs -> last xs

let rec init (l:list<'a>) : list<'a> =
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
    | FStar.Const.Const_reify -> C_Reify
    | FStar.Const.Const_reflect l -> C_Reflect (Ident.path_of_lid l)
    | _ -> failwith (BU.format1 "unknown constant: %s" (Print.const_to_string c))

let rec inspect_ln (t:term) : term_view =
    let t = U.unascribe t in
    let t = U.un_uinst t in
    let t = U.unlazy_emb t in
    match t.n with
    | Tm_meta (t, _) ->
        inspect_ln t

    | Tm_name bv ->
        Tv_Var bv

    | Tm_bvar bv ->
        Tv_BVar bv

    | Tm_fvar fv ->
        Tv_FVar fv

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

    | Tm_type _ ->
        Tv_Type ()

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
        Tv_Uvar (Z.of_int_fs (UF.uvar_id ctx_u.ctx_uvar_head),
                (ctx_u, s))

    | Tm_let ((false, [lb]), t2) ->
        if lb.lbunivs <> [] then Tv_Unknown else
        begin match lb.lbname with
        | BU.Inr _ -> Tv_Unknown // no top level lets
        | BU.Inl bv ->
            // The type of `bv` should match `lb.lbtyp`
            Tv_Let (false, lb.lbattrs, bv, lb.lbdef, t2)
        end

    | Tm_let ((true, [lb]), t2) ->
        if lb.lbunivs <> [] then Tv_Unknown else
        begin match lb.lbname with
        | BU.Inr _  -> Tv_Unknown // no top level lets
        | BU.Inl bv -> Tv_Let (true, lb.lbattrs, bv, lb.lbdef, t2)
        end

    | Tm_match (t, brs) ->
        let rec inspect_pat p =
            match p.v with
            | Pat_constant c -> Pat_Constant (inspect_const c)
            | Pat_cons (fv, ps) -> Pat_Cons (fv, List.map (fun (p, b) -> inspect_pat p, b) ps)
            | Pat_var bv -> Pat_Var bv
            | Pat_wild bv -> Pat_Wild bv
            | Pat_dot_term (bv, t) -> Pat_Dot_Term (bv, t)
        in
        let brs = List.map (function (pat, _, t) -> (inspect_pat pat, t)) brs in
        Tv_Match (t, brs)

    | Tm_unknown ->
        Tv_Unknown

    | _ ->
        Err.log_issue t.pos (Err.Warning_CantInspect, BU.format2 "inspect_ln: outside of expected syntax (%s, %s)\n" (Print.tag_of_term t) (Print.term_to_string t));
        Tv_Unknown

let inspect_comp (c : comp) : comp_view =
    let get_dec (flags : list<cflag>) : option<term> =
        match List.tryFind (function DECREASES _ -> true | _ -> false) flags with
        | None -> None
        | Some (DECREASES t) -> Some t
        | _ -> failwith "impossible"
    in
    match c.n with
    | Total (t, _) -> C_Total (t, None)
    | GTotal (t, _) -> C_GTotal (t, None)
    | Comp ct -> begin
        if Ident.lid_equals ct.effect_name PC.effect_Lemma_lid then
            match ct.effect_args with
            | (pre,_)::(post,_)::(pats,_)::_ ->
                C_Lemma (pre, post, pats)
            | _ ->
                failwith "inspect_comp: Lemma does not have enough arguments?"
        else if Ident.lid_equals ct.effect_name PC.effect_Tot_lid then
            let md = get_dec ct.flags in
            C_Total (ct.result_typ, md)
        else if Ident.lid_equals ct.effect_name PC.effect_GTot_lid then
            let md = get_dec ct.flags in
            C_GTotal (ct.result_typ, md)
        else
            let inspect_arg (a, q) = (a, inspect_aqual q) in
            C_Eff ([], // ct.comp_univs,
                   Ident.path_of_lid ct.effect_name,
                   ct.result_typ,
                   List.map inspect_arg ct.effect_args)
      end

let pack_comp (cv : comp_view) : comp =
    match cv with
    | C_Total (t, None) -> mk_Total t
    | C_Total (t, Some d) ->
        let ct = { comp_univs=[U_zero]
                 ; effect_name=PC.effect_Tot_lid
                 ; result_typ = t
                 ; effect_args = []
                 ; flags = [DECREASES d] }
        in
        S.mk_Comp ct

    | C_GTotal (t, None) -> mk_GTotal t
    | C_GTotal (t, Some d) ->
        let ct = { comp_univs=[U_zero]
                 ; effect_name=PC.effect_GTot_lid
                 ; result_typ = t
                 ; effect_args = []
                 ; flags = [DECREASES d] }
        in
        S.mk_Comp ct

    | C_Lemma (pre, post, pats) ->
        let ct = { comp_univs  = []
                 ; effect_name = PC.effect_Lemma_lid
                 ; result_typ  = S.t_unit
                 ; effect_args = [S.as_arg pre; S.as_arg post; S.as_arg pats]
                 ; flags       = [] } in
        S.mk_Comp ct

    | C_Eff (us, ef, res, args) ->
        let pack_arg (a, q) = (a, pack_aqual q) in
        let ct = { comp_univs  = [] //us
                 ; effect_name = Ident.lid_of_path ef Range.dummyRange
                 ; result_typ  = res
                 ; effect_args = List.map pack_arg args
                 ; flags       = [] } in
        S.mk_Comp ct

let pack_const (c:vconst) : sconst =
    match c with
    | C_Unit         -> C.Const_unit
    | C_Int i        -> C.Const_int (Z.string_of_big_int i, None)
    | C_True         -> C.Const_bool true
    | C_False        -> C.Const_bool false
    | C_String s     -> C.Const_string (s, Range.dummyRange)
    | C_Range  r     -> C.Const_range r
    | C_Reify        -> C.Const_reify
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

    | Tv_App (l, (r, q)) ->
        let q' = pack_aqual q in
        U.mk_app l [(r, q')]

    | Tv_Abs (b, t) ->
        mk (Tm_abs ([b], t, None)) t.pos // TODO: effect?

    | Tv_Arrow (b, c) ->
        mk (Tm_arrow ([b], c)) c.pos

    | Tv_Type () ->
        U.ktype

    | Tv_Refine (bv, t) ->
        mk (Tm_refine (bv, t)) t.pos

    | Tv_Const c ->
        S.mk (Tm_constant (pack_const c)) Range.dummyRange

    | Tv_Uvar (u, ctx_u_s) ->
      S.mk (Tm_uvar ctx_u_s) Range.dummyRange

    | Tv_Let (false, attrs, bv, t1, t2) ->
        let lb = U.mk_letbinding (BU.Inl bv) [] bv.sort PC.effect_Tot_lid t1 attrs Range.dummyRange in
        S.mk (Tm_let ((false, [lb]), t2)) Range.dummyRange

    | Tv_Let (true, attrs, bv, t1, t2) ->
        let lb = U.mk_letbinding (BU.Inl bv) [] bv.sort PC.effect_Tot_lid t1 attrs Range.dummyRange in
        S.mk (Tm_let ((true, [lb]), t2)) Range.dummyRange

    | Tv_Match (t, brs) ->
        let wrap v = {v=v;p=Range.dummyRange} in
        let rec pack_pat p : S.pat =
            match p with
            | Pat_Constant c -> wrap <| Pat_constant (pack_const c)
            | Pat_Cons (fv, ps) -> wrap <| Pat_cons (fv, List.map (fun (p, b) -> pack_pat p, b) ps)
            | Pat_Var  bv -> wrap <| Pat_var bv
            | Pat_Wild bv -> wrap <| Pat_wild bv
            | Pat_Dot_Term (bv, t) -> wrap <| Pat_dot_term (bv, t)
        in
        let brs = List.map (function (pat, t) -> (pack_pat pat, None, t)) brs in
        S.mk (Tm_match (t, brs)) Range.dummyRange

    | Tv_AscribedT(e, t, tacopt) ->
        S.mk (Tm_ascribed(e, (BU.Inl t, tacopt), None)) Range.dummyRange

    | Tv_AscribedC(e, c, tacopt) ->
        S.mk (Tm_ascribed(e, (BU.Inr c, tacopt), None)) Range.dummyRange

    | Tv_Unknown ->
        S.mk Tm_unknown Range.dummyRange

let compare_bv (x:bv) (y:bv) : order =
    let n = S.order_bv x y in
    if n < 0 then Lt
    else if n = 0 then Eq
    else Gt

let is_free (x:bv) (t:term) : bool =
    U.is_free_in x t

let free_bvs (t:term) : list<bv> =
  Syntax.Free.names t |> BU.set_elements

let free_uvars (t:term) : list<Z.t> =
  Syntax.Free.uvars_uncached t
    |> BU.set_elements
    |> List.map (fun u -> Z.of_int_fs (UF.uvar_id u.ctx_uvar_head))

let lookup_attr (attr:term) (env:Env.env) : list<fv> =
    match (SS.compress attr).n with
    | Tm_fvar fv ->
        let ses = Env.lookup_attr env (Ident.string_of_lid (lid_of_fv fv)) in
        List.concatMap (fun se -> match U.lid_of_sigelt se with
                                  | None -> []
                                  // FIXME: Get a proper delta depth
                                  | Some l -> [S.lid_as_fv l (S.Delta_constant_at_level 999) None]) ses
    | _ -> []

let all_defs_in_env (env:Env.env) : list<fv> =
    List.map (fun l -> S.lid_as_fv l (S.Delta_constant_at_level 999) None) (Env.lidents env) // |> take 10

let defs_in_module (env:Env.env) (modul:name) : list<fv> =
    List.concatMap
        (fun l ->
                (* must succeed, ids_of_lid always returns a non-empty list *)
                let ns = Ident.ids_of_lid l |> init |> List.map Ident.string_of_id in
                if ns = modul
                then [S.lid_as_fv l (S.Delta_constant_at_level 999) None]
                else [])
        (Env.lidents env)

let lookup_typ (env:Env.env) (ns:list<string>) : option<sigelt> =
    let lid = PC.p2l ns in
    Env.lookup_sigelt env lid

let sigelt_attrs (se : sigelt) : list<attribute> =
    se.sigattrs

let set_sigelt_attrs (attrs : list<attribute>) (se : sigelt) : sigelt =
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


let sigelt_quals (se : sigelt) : list<RD.qualifier> =
    se.sigquals |> List.map syntax_to_rd_qual

let set_sigelt_quals (quals : list<RD.qualifier>) (se : sigelt) : sigelt =
    { se with sigquals = List.map rd_to_syntax_qual quals }

let sigelt_opts (se : sigelt) : option<vconfig> = se.sigopts

let embed_vconfig (vcfg : vconfig) : term =
  EMB.embed EMB.e_vconfig vcfg Range.dummyRange None EMB.id_norm_cb

let inspect_sigelt (se : sigelt) : sigelt_view =
    match se.sigel with
    | Sig_let ((r, [lb]), _) ->
        let fv = match lb.lbname with
                 | BU.Inr fv -> fv
                 | BU.Inl _  -> failwith "impossible: global Sig_let has bv"
        in
        let s, us = SS.univ_var_opening lb.lbunivs in
        let typ = SS.subst s lb.lbtyp in
        let def = SS.subst s lb.lbdef in
        Sg_Let (r, fv, us, typ, def)

    | Sig_inductive_typ (lid, us, param_bs, ty, _mutual, c_lids) ->
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

    | _ ->
        Unk

let pack_sigelt (sv:sigelt_view) : sigelt =
    match sv with
    | Sg_Let (r, fv, univs, typ, def) ->
        let s = SS.univ_var_closing univs in
        let typ = SS.subst s typ in
        let def = SS.subst s def in
        let lb = U.mk_letbinding (BU.Inr fv) univs typ PC.effect_Tot_lid def [] def.pos in
        mk_sigelt <| Sig_let ((r, [lb]), [lid_of_fv fv])

    | Sg_Inductive (nm, us_names, param_bs, ty, ctors) ->
      let ind_lid = Ident.lid_of_path nm Range.dummyRange in
      let s = SS.univ_var_closing us_names in
      let nparam = List.length param_bs in

      let pack_ctor (c:ctor) : sigelt =
        let (nm, ty) = c in
        let lid = Ident.lid_of_path nm Range.dummyRange in
        let ty = U.arrow param_bs (S.mk_Total ty) in
        let ty = SS.subst s ty in (* close univs *)
        mk_sigelt <| Sig_datacon (lid, us_names, ty, ind_lid, nparam, [])
      in

      let ctor_ses : list<sigelt> = List.map pack_ctor ctors in
      let c_lids : list<Ident.lid> = List.map (fun se -> BU.must (U.lid_of_sigelt se)) ctor_ses in

      let ind_se : sigelt =
        let param_bs = SS.close_binders param_bs in
        let ty = SS.close param_bs ty in

        (* close univs *)
        let param_bs = SS.subst_binders s param_bs in
        let ty = SS.subst s ty in

        mk_sigelt <| Sig_inductive_typ (ind_lid, us_names, param_bs, ty, [], c_lids)
      in
      let se = mk_sigelt <| Sig_bundle (ind_se::ctor_ses, ind_lid::c_lids) in
      { se with sigquals = Noeq::se.sigquals }

    | Unk ->
        failwith "packing Unk, sorry"

let inspect_bv (bv:bv) : bv_view =
    {
      bv_ppname = Ident.string_of_id bv.ppname;
      bv_index = Z.of_int_fs bv.index;
      bv_sort = bv.sort;
    }

let pack_bv (bvv:bv_view) : bv =
    {
      ppname = Ident.mk_ident (bvv.bv_ppname, Range.dummyRange);
      index = Z.to_int_fs bvv.bv_index;
      sort = bvv.bv_sort;
    }

let inspect_binder (b:binder) : bv * aqualv =
    b.binder_bv, inspect_aqual (b.binder_qual)

let pack_binder (bv:bv) (aqv:aqualv) : binder =
    { binder_bv=bv; binder_qual=pack_aqual aqv; binder_attrs=[] }  //TODO: AR: should take attrs too

open FStar.TypeChecker.Env
let moduleof (e : Env.env) : list<string> =
    Ident.path_of_lid e.curmodule

let env_open_modules (e : Env.env) : list<name> =
    List.map (fun (l, m) -> List.map Ident.string_of_id (Ident.ids_of_lid l))
             (DsEnv.open_modules e.dsenv)

let binders_of_env e = FStar.TypeChecker.Env.all_binders e
let term_eq t1 t2 = U.term_eq (U.un_uinst t1) (U.un_uinst t2) // temporary, until universes are exposed
let term_to_string t = Print.term_to_string t
let comp_to_string c = Print.comp_to_string c

let implode_qn ns = String.concat "." ns
let explode_qn s = String.split ['.'] s
let compare_string s1 s2 = Z.of_int_fs (String.compare s1 s2)

let push_binder e b = Env.push_binders e [b]

let subst (x:bv) (n:term) (m:term) : term =
  SS.subst [NT(x,n)] m
