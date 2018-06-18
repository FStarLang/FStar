#light "off"
module FStar.Reflection.Basic

open FStar
open FStar.All
open FStar.Reflection.Data
open FStar.Syntax.Syntax
open FStar.Order
open FStar.Errors

module S = FStar.Syntax.Syntax // TODO: remove, it's open

module C = FStar.Const
module PC = FStar.Parser.Const
module SS = FStar.Syntax.Subst
module BU = FStar.Util
module Range = FStar.Range
module U = FStar.Syntax.Util
module UF = FStar.Syntax.Unionfind
module Print = FStar.Syntax.Print
module Ident = FStar.Ident
module Env = FStar.TypeChecker.Env
module Err = FStar.Errors
module Z = FStar.BigInt

open FStar.Dyn

(* This file provides implementation for reflection primitives in F*.
 *
 * Users can be exposed to (mostly) raw syntax of terms when working in
 * a metaprogramming effect (such as TAC). These effects are irrelevant
 * for runtime and cannot, of course, be used for proof (where syntax
 * inspection would be completely inconsistent
 *
 * embed   : from compiler to user
 * unembed : from user to compiler
 *)

 (*
  * Most of this file is tedious and repetitive.
  * We should really allow for some metaprogramming in F*. Oh wait....
  *)

(* private *)
let inspect_aqual (aq : aqual) : aqualv =
    match aq with
    | Some (Meta _) -> failwith "Sorry! cannot inspect TC arguments for now"
    | Some (Implicit _) -> Data.Q_Implicit
    | Some Equality
    | None -> Data.Q_Explicit

(* private *)
let pack_aqual (aqv : aqualv) : aqual =
    match aqv with
    | Data.Q_Explicit -> None
    | Data.Q_Implicit -> Some (Implicit false)

let inspect_fv (fv:fv) : list<string> =
    Ident.path_of_lid (lid_of_fv fv)

let pack_fv (ns:list<string>) : fv =
    let lid = PC.p2l ns in
    let attr =
        if Ident.lid_equals lid PC.cons_lid then Some Data_ctor else
        if Ident.lid_equals lid PC.nil_lid  then Some Data_ctor else
        if Ident.lid_equals lid PC.some_lid then Some Data_ctor else
        if Ident.lid_equals lid PC.none_lid then Some Data_ctor else
        None
    in
    lid_as_fv (PC.p2l ns) (Delta_constant_at_level 999) attr

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
    | _ -> failwith (BU.format1 "unknown constant: %s" (Print.const_to_string c))

let rec inspect_ln (t:term) : term_view =
    let t = U.unascribe t in
    let t = U.un_uinst t in
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
        Tv_App (S.mk_Tm_app hd (init args) None t.pos, (a, q')) // TODO: The range and tk are probably wrong. Fix

    | Tm_abs ([], _, _) ->
        failwith "inspect_ln: empty arguments on Tm_abs"

    | Tm_abs (b::bs, t, k) ->
        let body =
            match bs with
            | [] -> t
            | bs -> S.mk (Tm_abs (bs, t, k)) None t.pos
        in
        Tv_Abs (b, body)

    | Tm_type _ ->
        Tv_Type ()

    | Tm_arrow ([], k) ->
        failwith "inspect_ln: empty binders on arrow"

    | Tm_arrow _ ->
        begin match U.arrow_one t with
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
            Tv_Let (false, bv, lb.lbdef, t2)
        end

    | Tm_let ((true, [lb]), t2) ->
        if lb.lbunivs <> [] then Tv_Unknown else
        begin match lb.lbname with
        | BU.Inr _  -> Tv_Unknown // no top level lets
        | BU.Inl bv -> Tv_Let (true, bv, lb.lbdef, t2)
        end

    | Tm_match (t, brs) ->
        let rec inspect_pat p =
            match p.v with
            | Pat_constant c -> Pat_Constant (inspect_const c)
            | Pat_cons (fv, ps) -> Pat_Cons (fv, List.map (fun (p, _) -> inspect_pat p) ps)
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
    match c.n with
    | Total (t, _) -> C_Total (t, None)
    | Comp ct -> begin
        if Ident.lid_equals ct.effect_name PC.effect_Lemma_lid then
            match ct.effect_args with
            | (pre,_)::(post,_)::_ ->
                C_Lemma (pre, post)
            | _ ->
                failwith "inspect_comp: Lemma does not have enough arguments?"
        else if Ident.lid_equals ct.effect_name PC.effect_Tot_lid then
            let maybe_dec = List.tryFind (function DECREASES _ -> true | _ -> false) ct.flags in
            let md = match maybe_dec with
                     | None -> None
                     | Some (DECREASES t) -> Some t
                     | _ -> failwith "impossible"
            in
            C_Total (ct.result_typ, md)
        else
            C_Unknown
      end
    | GTotal _ -> C_Unknown

let pack_comp (cv : comp_view) : comp =
    match cv with
    | C_Total (t, _) -> mk_Total t
    | _ -> failwith "sorry, can embed comp_views other than C_Total for now"

let pack_const (c:vconst) : sconst =
    match c with
    | C_Unit    -> C.Const_unit
    | C_Int i   -> C.Const_int (Z.string_of_big_int i, None)
    | C_True    -> C.Const_bool true
    | C_False   -> C.Const_bool false
    | C_String s -> C.Const_string (s, Range.dummyRange)

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
        U.abs [b] t None // TODO: effect?

    | Tv_Arrow (b, c) ->
        U.arrow [b] c

    | Tv_Type () ->
        U.ktype

    | Tv_Refine (bv, t) ->
        U.refine bv t

    | Tv_Const c ->
        S.mk (Tm_constant (pack_const c)) None Range.dummyRange

    | Tv_Uvar (u, ctx_u_s) ->
      S.mk (Tm_uvar ctx_u_s) None Range.dummyRange

    | Tv_Let (false, bv, t1, t2) ->
        let lb = U.mk_letbinding (BU.Inl bv) [] bv.sort PC.effect_Tot_lid t1 [] Range.dummyRange in
        S.mk (Tm_let ((false, [lb]), t2)) None Range.dummyRange

    | Tv_Let (true, bv, t1, t2) ->
        let lb = U.mk_letbinding (BU.Inl bv) [] bv.sort PC.effect_Tot_lid t1 [] Range.dummyRange in
        S.mk (Tm_let ((true, [lb]), t2)) None Range.dummyRange

    | Tv_Match (t, brs) ->
        let wrap v = {v=v;p=Range.dummyRange} in
        let rec pack_pat p : S.pat =
            match p with
            | Pat_Constant c -> wrap <| Pat_constant (pack_const c)
            | Pat_Cons (fv, ps) -> wrap <| Pat_cons (fv, List.map (fun p -> pack_pat p, false) ps)
            | Pat_Var  bv -> wrap <| Pat_var bv
            | Pat_Wild bv -> wrap <| Pat_wild bv
            | Pat_Dot_Term (bv, t) -> wrap <| Pat_dot_term (bv, t)
        in
        let brs = List.map (function (pat, t) -> (pack_pat pat, None, t)) brs in
        S.mk (Tm_match (t, brs)) None Range.dummyRange

    | Tv_AscribedT(e, t, tacopt) ->
        S.mk (Tm_ascribed(e, (BU.Inl t, tacopt), None)) None Range.dummyRange

    | Tv_AscribedC(e, c, tacopt) ->
        S.mk (Tm_ascribed(e, (BU.Inr c, tacopt), None)) None Range.dummyRange

    | Tv_Unknown ->
        S.mk Tm_unknown None Range.dummyRange

let compare_bv (x:bv) (y:bv) : order =
    let n = S.order_bv x y in
    if n < 0 then Lt
    else if n = 0 then Eq
    else Gt

let is_free (x:bv) (t:term) : bool =
    U.is_free_in x t

let lookup_attr (attr:term) (env:Env.env) : list<fv> =
    match (SS.compress attr).n with
    | Tm_fvar fv ->
        let ses = Env.lookup_attr env (Ident.text_of_lid (lid_of_fv fv)) in
        List.concatMap (fun se -> match U.lid_of_sigelt se with
                                  | None -> []
                                  | Some l -> [S.lid_as_fv l S.delta_constant None]) ses
    | _ -> []

let lookup_typ (env:Env.env) (ns:list<string>) : option<sigelt> =
    let lid = PC.p2l ns in
    match Env.lookup_qname env lid with
    | None -> None
    | Some (BU.Inl _, rng) -> None
    | Some (BU.Inr (se, us), rng) -> Some se

let inspect_sigelt (se : sigelt) : sigelt_view =
    match se.sigel with
    | Sig_let ((r, [lb]), _) ->
        let fv = match lb.lbname with
                 | BU.Inr fv -> fv
                 | BU.Inl _  -> failwith "global Sig_let has bv"
        in
        Sg_Let (r, fv, lb.lbtyp, lb.lbdef)

    | Sig_inductive_typ (lid, us, bs, t, _, c_lids) ->
        let nm = Ident.path_of_lid lid in
        Sg_Inductive (nm, bs, t, List.map Ident.path_of_lid c_lids)

    | Sig_datacon (lid, us, t, _, n, _) ->
        Sg_Constructor (Ident.path_of_lid lid, t)

    | _ ->
        Unk

let pack_sigelt (sv:sigelt_view) : sigelt =
    match sv with
    | Sg_Let (r, fv, ty, def) ->
        let lb = U.mk_letbinding (BU.Inr fv) [] ty PC.effect_Tot_lid def [] def.pos in
        mk_sigelt <| Sig_let ((r, [lb]), [lid_of_fv fv])

    | Sg_Constructor _ ->
        failwith "packing Sg_Constructor, sorry"

    | Sg_Inductive _ ->
        failwith "packing Sg_Inductive, sorry"

    | Unk ->
        failwith "packing Unk, sorry"

let inspect_bv (bv:bv) : bv_view =
    {
      bv_ppname = Ident.string_of_ident bv.ppname;
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
    let bv, aq = b in
    bv, inspect_aqual aq

let pack_binder (bv:bv) (aqv:aqualv) : binder =
    bv, pack_aqual aqv

open FStar.TypeChecker.Env
let moduleof (e : Env.env) : list<string> =
    Ident.path_of_lid e.curmodule

let binders_of_env e = FStar.TypeChecker.Env.all_binders e
let term_eq t1 t2 = U.term_eq (U.un_uinst t1) (U.un_uinst t2) // temporary, until universes are exposed
let term_to_string t = Print.term_to_string t
