#light "off"
module FStar.Reflection.Basic

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

let inspect_fv (fv:fv) : list<string> =
    Ident.path_of_lid (lid_of_fv fv)

let pack_fv (ns:list<string>) : fv =
    lid_as_fv (PC.p2l ns) (Delta_defined_at_level 999) None

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

let inspect_bv (b:binder) : string =
    Print.bv_to_string (fst b)
    // calling into Print, which really doesn't make guarantees
    // ... should be safe as we give no semantics to these names: they're just for debugging

let inspect_const (c:sconst) : vconst =
    match c with
    | FStar.Const.Const_unit -> C_Unit
    | FStar.Const.Const_int (s, _) -> C_Int (Z.big_int_of_string s)
    | FStar.Const.Const_bool true  -> C_True
    | FStar.Const.Const_bool false -> C_False
    | FStar.Const.Const_string (s, _) -> C_String s
    | _ -> failwith (BU.format1 "unknown constant: %s" (Print.const_to_string c))

let rec inspect (t:term) : term_view =
    let t = U.unascribe t in
    let t = U.un_uinst t in
    match t.n with
    | Tm_meta (t, _) ->
        inspect t

    | Tm_name bv ->
        Tv_Var (S.mk_binder bv)

    | Tm_fvar fv ->
        Tv_FVar fv

    | Tm_app (hd, []) ->
        failwith "inspect: empty arguments on Tm_app"

    | Tm_app (hd, args) ->
        // We split at the last argument, since the term_view does not
        // expose n-ary lambdas buy unary ones.
        let (a, q) = last args in
        let q' = match q with
                 | Some (Implicit _) -> Data.Q_Implicit
                 | Some Equality
                 | None -> Data.Q_Explicit
        in
        Tv_App (S.mk_Tm_app hd (init args) None t.pos, (a, q')) // TODO: The range and tk are probably wrong. Fix

    | Tm_abs ([], _, _) ->
        failwith "inspect: empty arguments on Tm_abs"

    | Tm_abs (bs, t, k) ->
        let bs, t = SS.open_term bs t in
        // `let b::bs = bs` gives a coverage warning, avoid it
        begin match bs with
        | [] -> failwith "impossible"
        | b::bs -> Tv_Abs (b, U.abs bs t k)
        end

    | Tm_type _ ->
        Tv_Type ()

    | Tm_arrow ([], k) ->
        failwith "inspect: empty binders on arrow"

    | Tm_arrow _ ->
        begin match U.arrow_one t with
        | Some (b, c) -> Tv_Arrow (b, c)
        | None -> failwith "impossible"
        end

    | Tm_refine (bv, t) ->
        let b = S.mk_binder bv in
        let b', t = SS.open_term [b] t in
        // `let [b] = b'` gives a coverage warning, avoid it
        let b = (match b' with
        | [b'] -> b'
        | _ -> failwith "impossible") in
        Tv_Refine (b, t)

    | Tm_constant c ->
        Tv_Const (inspect_const c)

    | Tm_uvar (u, t) ->
        Tv_Uvar (Z.of_int_fs (UF.uvar_id u), t)

    | Tm_let ((false, [lb]), t2) ->
        if lb.lbunivs <> [] then Tv_Unknown else
        begin match lb.lbname with
        | BU.Inr _ -> Tv_Unknown // no top level lets
        | BU.Inl bv ->
            // The type of `bv` should match `lb.lbtyp`
            let b = S.mk_binder bv in
            let bs, t2 = SS.open_term [b] t2 in
            let b = match bs with
                    | [b] -> b
                    | _ -> failwith "impossible: open_term returned different amount of binders"
            in
            Tv_Let (false, b, lb.lbdef, t2)
        end

    | Tm_let ((true, [lb]), t2) ->
        if lb.lbunivs <> [] then Tv_Unknown else
        begin match lb.lbname with
        | BU.Inr _ -> Tv_Unknown // no top level lets
        | BU.Inl bv ->
            let lbs, t2 = SS.open_let_rec [lb] t2 in
            match lbs with
            | [lb] ->
                (match lb.lbname with
                 | BU.Inr _ -> Tv_Unknown
                 | BU.Inl bv -> Tv_Let (true, S.mk_binder bv, lb.lbdef, t2))
            | _ -> failwith "impossible: open_term returned different amount of binders"
        end

    | Tm_match (t, brs) ->
        let rec inspect_pat p =
            match p.v with
            | Pat_constant c -> Pat_Constant (inspect_const c)
            | Pat_cons (fv, ps) -> Pat_Cons (fv, List.map (fun (p, _) -> inspect_pat p) ps)
            | Pat_var bv -> Pat_Var (S.mk_binder bv)
            | Pat_wild bv -> Pat_Wild (S.mk_binder bv)
            | Pat_dot_term _ -> failwith "NYI: Pat_dot_term"
        in
        let brs = List.map SS.open_branch brs in
        let brs = List.map (function (pat, _, t) -> (inspect_pat pat, t)) brs in
        Tv_Match (t, brs)

    | _ ->
        Err.log_issue t.pos (Err.Warning_CantInspect, BU.format2 "inspect: outside of expected syntax (%s, %s)\n" (Print.tag_of_term t) (Print.term_to_string t));
        Tv_Unknown

let inspect_comp (c : comp) : comp_view =
    match c.n with
    | Total (t, _) -> C_Total t
    | Comp ct -> begin
        if Ident.lid_equals ct.effect_name PC.effect_Lemma_lid then
            match ct.effect_args with
            | (pre,_)::(post,_)::_ ->
                C_Lemma (pre, post)
            | _ ->
                failwith "inspect_comp: Lemma does not have enough arguments?"
        else
            C_Unknown
      end
    | GTotal _ -> C_Unknown

let pack_comp (cv : comp_view) : comp =
    match cv with
    | C_Total t -> mk_Total t
    | _ -> failwith "sorry, can embed comp_views other than C_Total for now"

let pack_const (c:vconst) : sconst =
    match c with
    | C_Unit    -> C.Const_unit
    | C_Int i   -> C.Const_int (Z.string_of_big_int i, None)
    | C_True    -> C.Const_bool true
    | C_False   -> C.Const_bool false
    | C_String s -> C.Const_string (s, Range.dummyRange)

// TODO: pass in range?
let pack (tv:term_view) : term =
    match tv with
    | Tv_Var (bv, _) ->
        S.bv_to_name bv

    | Tv_FVar fv ->
        S.fv_to_tm fv

    | Tv_App (l, (r, q)) ->
        begin match q with
        | Data.Q_Explicit -> U.mk_app l [S.as_arg r]
        | Data.Q_Implicit -> U.mk_app l [S.iarg r]
        end

    | Tv_Abs (b, t) ->
        U.abs [b] t None // TODO: effect?

    | Tv_Arrow (b, c) ->
        U.arrow [b] c

    | Tv_Type () ->
        U.ktype

    | Tv_Refine ((bv, _), t) ->
        U.refine bv t

    | Tv_Const c ->
        S.mk (Tm_constant (pack_const c)) None Range.dummyRange

    | Tv_Uvar (u, t) ->
        U.uvar_from_id (Z.to_int_fs u) t

    | Tv_Let (false, b, t1, t2) ->
        let bv = fst b in
        let lb = U.mk_letbinding (BU.Inl bv) [] bv.sort PC.effect_Tot_lid t1 [] Range.dummyRange in
        S.mk (Tm_let ((false, [lb]), SS.close [b] t2)) None Range.dummyRange

    | Tv_Let (true, b, t1, t2) ->
        let bv = fst b in
        let lb = U.mk_letbinding (BU.Inl bv) [] bv.sort PC.effect_Tot_lid t1 [] Range.dummyRange in
        let lbs_open, body_open = SS.open_let_rec [lb] t2 in
        let lbs, body = SS.close_let_rec [lb] body_open in
        S.mk (Tm_let ((true, lbs), body)) None Range.dummyRange

    | Tv_Match (t, brs) ->
        let wrap v = {v=v;p=Range.dummyRange} in
        let rec pack_pat p : S.pat =
            match p with
            | Pat_Constant c -> wrap <| Pat_constant (pack_const c)
            | Pat_Cons (fv, ps) -> wrap <| Pat_cons (fv, List.map (fun p -> pack_pat p, false) ps)
            | Pat_Var  (bv, _) -> wrap <| Pat_var bv
            | Pat_Wild (bv,_ ) -> wrap <| Pat_wild bv
        in
        let brs = List.map (function (pat, t) -> (pack_pat pat, None, t)) brs in
        let brs = List.map SS.close_branch brs in
        S.mk (Tm_match (t, brs)) None Range.dummyRange

    | Tv_Unknown ->
        failwith "pack: unexpected term view"

let compare_binder (x:binder) (y:binder) : order =
    let n = S.order_bv (fst x) (fst y) in
    if n < 0 then Lt
    else if n = 0 then Eq
    else Gt

let is_free (x:binder) (t:term) : bool =
    U.is_free_in (fst x) t

// Only for inductives, at the moment
let lookup_typ (env:Env.env) (ns:list<string>) : sigelt_view =
    let lid = PC.p2l ns in
    let res = Env.lookup_qname env lid in
    match res with
    | None ->
        Unk
    | Some (BU.Inl _, rng) ->
        Unk
    | Some (BU.Inr (se, us), rng) ->
        begin match se.sigel with
        | Sig_inductive_typ (lid, us, bs, t, _, dc_lids) ->
            let nm = Ident.path_of_lid lid in
            let ctor1 dc_lid =
                begin match Env.lookup_qname env dc_lid with
                | Some (BU.Inr (se, us), rng) ->
                    begin match se.sigel with
                    | Sig_datacon (lid, us, t, _, n, _) ->
                        Ctor (Ident.path_of_lid lid, t)
                    | _ -> failwith "wat 1"
                    end
                | _ -> failwith "wat 2"
                end
            in
            let ctors = List.map ctor1 dc_lids in
            Sg_Inductive (nm, bs, t, ctors)
        | Sig_let ((false, [lb]), _) ->
            let fv = match lb.lbname with
                     | BU.Inr fv -> fv
                     | BU.Inl _  -> failwith "global Sig_let has bv"
            in
            Sg_Let (fv, lb.lbtyp, lb.lbdef)

        | _ ->
            Unk
        end

let binders_of_env e = FStar.TypeChecker.Env.all_binders e
let type_of_binder (b : binder) = match b with (b, _) -> b.sort
let term_eq t1 t2 = U.term_eq (U.un_uinst t1) (U.un_uinst t2) // temporary, until universes are exposed
let term_to_string t = Print.term_to_string t
