#light "off"
module FStar.Reflection.Basic

open FStar.All
open FStar.Reflection.Data
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Order

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

(* This file provides implementation for reflection primitives in F*.
 *
 * Users can be exposed to (mostly) raw syntax of terms when working in
 * a metaprogramming effect (such as TAC). These effects are irrelevant
 * for runtime and cannot, of course, be used for proof (where syntax
 * inspection would be completely inconsistent
 *
 * embed   : from compiler to user
 * unembed : from user to compiler
 *
 * TODO: decide if the term_view datatype has any use within the compiler.
 * If not, `inspect` and `embed_term_view` could be coallesced, although
 * I'm not sure if that's an actual gain.
 *)

 (*
  * Most of this file is tedious and repetitive.
  * We should really allow for some metaprogramming in F*. Oh wait....
  *)

let lid_as_tm l = S.lid_as_fv l Delta_constant None |> S.fv_to_tm
let fstar_refl_embed = lid_as_tm PC.fstar_refl_embed_lid

let protect_embedded_term (t:typ) (x:term) =
    S.mk_Tm_app fstar_refl_embed [S.iarg t; S.as_arg x] None x.pos

let un_protect_embedded_term (t : term) : term =
    let head, args = U.head_and_args (U.unmeta t) in
    match (U.un_uinst head).n, args with
    | Tm_fvar fv, [_; (x, _)]
        when S.fv_eq_lid fv PC.fstar_refl_embed_lid ->
      x
    | _ ->
      failwith (BU.format1 "Not a protected embedded term: %s" (Print.term_to_string t))

let embed_binder (b:binder) : term =
    U.mk_alien fstar_refl_binder b "reflection.embed_binder" None

let unembed_binder (t:term) : binder =
    U.un_alien t |> FStar.Dyn.undyn

let embed_binders l = embed_list embed_binder fstar_refl_binder l
let unembed_binders t = unembed_list unembed_binder t

let embed_term (t:term) : term =
    protect_embedded_term S.tun t

let unembed_term (t:term) : term =
    un_protect_embedded_term t

let embed_fvar (fv:fv) : term =
    U.mk_alien fstar_refl_fvar fv "reflection.embed_fvar" None

let unembed_fvar (t:term) : fv =
    U.un_alien t |> FStar.Dyn.undyn

let embed_comp (c:comp) : term =
    U.mk_alien fstar_refl_comp c "reflection.embed_comp" None

let unembed_comp (t:term) : comp =
    U.un_alien t |> FStar.Dyn.undyn

let embed_env (env:Env.env) : term =
    U.mk_alien fstar_refl_env env "tactics_embed_env" None

let unembed_env (t:term) : Env.env =
    U.un_alien t |> FStar.Dyn.undyn

let embed_const (c:vconst) : term =
    match c with
    | C_Unit    -> ref_C_Unit
    | C_True    -> ref_C_True
    | C_False   -> ref_C_False

    | C_Int i ->
        S.mk_Tm_app ref_C_Int [S.as_arg (U.exp_int (BU.string_of_int i))]
                    None Range.dummyRange
    | C_String s ->
        S.mk_Tm_app ref_C_String [S.as_arg (embed_string s)]
                    None Range.dummyRange

let unembed_const (t:term) : vconst =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_C_Unit_lid ->
        C_Unit

    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_C_True_lid ->
        C_True

    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_C_False_lid ->
        C_False

    | Tm_fvar fv, [(i, _)] when S.fv_eq_lid fv ref_C_Int_lid ->
        C_Int (unembed_int i)

    | Tm_fvar fv, [(s, _)] when S.fv_eq_lid fv ref_C_String_lid ->
        C_String (unembed_string s)

    | _ ->
        failwith "not an embedded vconst"

let rec embed_pattern (p : pattern) : term =
    match p with
    | Pat_Constant c ->
        S.mk_Tm_app ref_Pat_Constant [S.as_arg (embed_const c)] None Range.dummyRange
    | Pat_Cons (fv, ps) ->
        S.mk_Tm_app ref_Pat_Cons [S.as_arg (embed_fvar fv); S.as_arg (embed_list embed_pattern fstar_refl_pattern ps)] None Range.dummyRange
    | Pat_Var bv ->
        S.mk_Tm_app ref_Pat_Var [S.as_arg (embed_binder (S.mk_binder bv))] None Range.dummyRange
    | Pat_Wild bv ->
        S.mk_Tm_app ref_Pat_Wild [S.as_arg (embed_binder (S.mk_binder bv))] None Range.dummyRange

let rec unembed_pattern (t : term) : pattern =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(c, _)] when S.fv_eq_lid fv ref_Pat_Constant_lid ->
        Pat_Constant (unembed_const c)
    | Tm_fvar fv, [(f, _); (ps, _)] when S.fv_eq_lid fv ref_Pat_Cons_lid ->
        Pat_Cons (unembed_fvar f, unembed_list unembed_pattern ps)
    | Tm_fvar fv, [(b, _)] when S.fv_eq_lid fv ref_Pat_Var_lid ->
        Pat_Var (fst (unembed_binder b))
    | Tm_fvar fv, [(b, _)] when S.fv_eq_lid fv ref_Pat_Wild_lid ->
        Pat_Wild (fst (unembed_binder b))
    | _ ->
        failwith "not an embedded pattern"

let embed_branch = embed_pair embed_pattern fstar_refl_pattern embed_term S.t_term
let unembed_branch = unembed_pair unembed_pattern unembed_term

let embed_aqualv (q : aqualv) : term =
    match q with
    | Data.Q_Explicit -> ref_Q_Explicit
    | Data.Q_Implicit -> ref_Q_Implicit
let unembed_aqualv (t : term) : aqualv =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Q_Explicit_lid -> Data.Q_Explicit
    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Q_Implicit_lid -> Data.Q_Implicit
    | _ ->
        failwith "not an embedded aqualv"

let embed_argv = embed_pair embed_term S.t_term embed_aqualv fstar_refl_aqualv
let unembed_argv = unembed_pair unembed_term unembed_aqualv

let embed_term_view (t:term_view) : term =
    match t with
    | Tv_FVar fv ->
        S.mk_Tm_app ref_Tv_FVar [S.as_arg (embed_fvar fv)]
                    None Range.dummyRange

    | Tv_Var bv ->
        S.mk_Tm_app ref_Tv_Var [S.as_arg (embed_binder bv)]
                    None Range.dummyRange

    | Tv_App (hd, a) ->
        S.mk_Tm_app ref_Tv_App [S.as_arg (embed_term hd); S.as_arg (embed_argv a)]
                    None Range.dummyRange

    | Tv_Abs (b, t) ->
        S.mk_Tm_app ref_Tv_Abs [S.as_arg (embed_binder b); S.as_arg (embed_term t)]
                    None Range.dummyRange

    | Tv_Arrow (b, c) ->
        S.mk_Tm_app ref_Tv_Arrow [S.as_arg (embed_binder b); S.as_arg (embed_comp c)]
                    None Range.dummyRange

    | Tv_Type u ->
        S.mk_Tm_app ref_Tv_Type [S.as_arg (embed_unit ())]
                    None Range.dummyRange

    | Tv_Refine (bv, t) ->
        S.mk_Tm_app ref_Tv_Refine [S.as_arg (embed_binder bv); S.as_arg (embed_term t)]
                    None Range.dummyRange

    | Tv_Const c ->
        S.mk_Tm_app ref_Tv_Const [S.as_arg (embed_const c)]
                    None Range.dummyRange

    | Tv_Uvar (u, t) ->
        S.mk_Tm_app ref_Tv_Uvar [S.as_arg (embed_int u); S.as_arg (embed_term t)]
                    None Range.dummyRange

    | Tv_Let (b, t1, t2) ->
        S.mk_Tm_app ref_Tv_Let [S.as_arg (embed_binder b); S.as_arg (embed_term t1); S.as_arg (embed_term t2)]
                    None Range.dummyRange

    | Tv_Match (t, brs) ->
        S.mk_Tm_app ref_Tv_Match [S.as_arg (embed_term t); S.as_arg (embed_list embed_branch fstar_refl_branch brs)]
                    None Range.dummyRange

    | Tv_Unknown ->
        ref_Tv_Unknown

let unembed_term_view (t:term) : term_view =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(b, _)] when S.fv_eq_lid fv ref_Tv_Var_lid ->
        Tv_Var (unembed_binder b)

    | Tm_fvar fv, [(b, _)] when S.fv_eq_lid fv ref_Tv_FVar_lid ->
        Tv_FVar (unembed_fvar b)

    | Tm_fvar fv, [(l, _); (r, _)] when S.fv_eq_lid fv ref_Tv_App_lid ->
        Tv_App (unembed_term l, unembed_argv r)

    | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Abs_lid ->
        Tv_Abs (unembed_binder b, unembed_term t)

    | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Arrow_lid ->
        Tv_Arrow (unembed_binder b, unembed_comp t)

    | Tm_fvar fv, [(u, _)] when S.fv_eq_lid fv ref_Tv_Type_lid ->
        Tv_Type (unembed_unit u)

    | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Refine_lid ->
        Tv_Refine (unembed_binder b, unembed_term t)

    | Tm_fvar fv, [(c, _)] when S.fv_eq_lid fv ref_Tv_Const_lid ->
        Tv_Const (unembed_const c)

    | Tm_fvar fv, [(u, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Uvar_lid ->
        Tv_Uvar (unembed_int u, unembed_term t)

    | Tm_fvar fv, [(b, _); (t1, _); (t2, _)] when S.fv_eq_lid fv ref_Tv_Let_lid ->
        Tv_Let (unembed_binder b, unembed_term t1, unembed_term t2)

    | Tm_fvar fv, [(t, _); (brs, _)] when S.fv_eq_lid fv ref_Tv_Match_lid ->
        Tv_Match (unembed_term t, unembed_list unembed_branch brs)

    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Tv_Unknown_lid ->
        Tv_Unknown

    | _ ->
        failwith "not an embedded term_view"

let embed_comp_view (cv : comp_view) : term =
    match cv with
    | C_Total t ->
        S.mk_Tm_app ref_C_Total [S.as_arg (embed_term t)]
                    None Range.dummyRange

    | C_Lemma (pre, post) ->
        S.mk_Tm_app ref_C_Lemma [S.as_arg (embed_term pre); S.as_arg (embed_term post)]
                    None Range.dummyRange

    | C_Unknown ->
        ref_C_Unknown

let unembed_comp_view (t : term) : comp_view =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(t, _)] when S.fv_eq_lid fv ref_C_Total_lid ->
        C_Total (unembed_term t)

    | Tm_fvar fv, [(pre, _); (post, _)] when S.fv_eq_lid fv ref_C_Lemma_lid ->
        C_Lemma (unembed_term pre, unembed_term post)

    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_C_Unknown_lid ->
        C_Unknown

    | _ ->
        failwith "not an embedded comp_view"

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

let inspect_fv (fv:fv) : list<string> =
    Ident.path_of_lid (lid_of_fv fv)

let pack_fv (ns:list<string>) : fv =
    // TODO: Delta_equational and None ok?
    lid_as_fv (PC.p2l ns) Delta_equational None

let inspect_bv (b:binder) : string =
    Print.bv_to_string (fst b)
    // calling into Print, which really doesn't make guarantees
    // ... should be safe as we give no semantics to these names: they're just for debugging

let inspect_const (c:sconst) : vconst =
    match c with
    | FStar.Const.Const_unit -> C_Unit
    | FStar.Const.Const_int (s, _) -> C_Int (BU.int_of_string s)
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
        Tv_Uvar (UF.uvar_id u, t)

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
            Tv_Let (b, lb.lbdef, t2)
        end

    | Tm_match (t, brs) ->
        let rec inspect_pat p =
            match p.v with
            | Pat_constant c -> Pat_Constant (inspect_const c)
            | Pat_cons (fv, ps) -> Pat_Cons (fv, List.map (fun (p, _) -> inspect_pat p) ps)
            | Pat_var bv -> Pat_Var bv
            | Pat_wild bv -> Pat_Wild bv
            | Pat_dot_term _ -> failwith "NYI: Pat_dot_term"
        in
        let brs = List.map SS.open_branch brs in
        let brs = List.map (function (pat, _, t) -> (inspect_pat pat, t)) brs in
        Tv_Match (t, brs)

    | _ ->
        BU.print2 "inspect: outside of expected syntax (%s, %s)\n" (Print.tag_of_term t) (Print.term_to_string t);
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
    | C_Int i   -> C.Const_int (BU.string_of_int i, None)
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
        U.uvar_from_id u t

    | Tv_Let (b, t1, t2) ->
        let bv = fst b in
        let lb = U.mk_letbinding (BU.Inl bv) [] bv.sort PC.effect_Tot_lid t1 in
        S.mk (Tm_let ((false, [lb]), SS.close [b] t2)) None Range.dummyRange

    | Tv_Match (t, brs) ->
        let wrap v = {v=v;p=Range.dummyRange} in
        let rec pack_pat p : S.pat =
            match p with
            | Pat_Constant c -> wrap <| Pat_constant (pack_const c)
            | Pat_Cons (fv, ps) -> wrap <| Pat_cons (fv, List.map (fun p -> pack_pat p, false) ps)
            | Pat_Var bv -> wrap <| Pat_var bv
            | Pat_Wild bv -> wrap <| Pat_wild bv
        in
        let brs = List.map (function (pat, t) -> (pack_pat pat, None, t)) brs in
        let brs = List.map SS.close_branch brs in
        S.mk (Tm_match (t, brs)) None Range.dummyRange

    | Tv_Unknown ->
        failwith "pack: unexpected term view"

let embed_order (o:order) : term =
    match o with
    | Lt -> ord_Lt
    | Eq -> ord_Eq
    | Gt -> ord_Gt

let unembed_order (t:term) : order =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [] when S.fv_eq_lid fv ord_Lt_lid -> Lt
    | Tm_fvar fv, [] when S.fv_eq_lid fv ord_Eq_lid -> Eq
    | Tm_fvar fv, [] when S.fv_eq_lid fv ord_Gt_lid -> Gt
    | _ -> failwith "not an embedded order"

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

let embed_ctor (c:ctor) : term =
    match c with
    | Ctor (nm, t) ->
        S.mk_Tm_app ref_Ctor
                    [S.as_arg (embed_string_list nm);
                     S.as_arg (embed_term t)]
                    None Range.dummyRange

let unembed_ctor (t:term) : ctor =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(nm, _); (t, _)] when S.fv_eq_lid fv ref_Ctor_lid ->
        Ctor (unembed_string_list nm, unembed_term t)
    | _ ->
        failwith "not an embedded ctor"

let embed_sigelt_view (sev:sigelt_view) : term =
    match sev with
    | Sg_Inductive (nm, bs, t, dcs) ->
        S.mk_Tm_app ref_Sg_Inductive
                    [S.as_arg (embed_string_list nm);
                        S.as_arg (embed_binders bs);
                        S.as_arg (embed_term t);
                        S.as_arg (embed_list embed_ctor fstar_refl_ctor dcs)]
                    None Range.dummyRange

    | Sg_Let (fv, ty, t) ->
        S.mk_Tm_app ref_Sg_Let
                    [S.as_arg (embed_fvar fv);
                        S.as_arg (embed_term ty);
                        S.as_arg (embed_term t)]
                    None Range.dummyRange

    | Unk ->
        ref_Unk

let unembed_sigelt_view (t:term) : sigelt_view =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(nm, _); (bs, _); (t, _); (dcs, _)] when S.fv_eq_lid fv ref_Sg_Inductive_lid ->
        Sg_Inductive (unembed_string_list nm, unembed_binders bs, unembed_term t, unembed_list unembed_ctor dcs)

    | Tm_fvar fv, [(fvar, _); (ty, _); (t, _)] when S.fv_eq_lid fv ref_Sg_Let_lid ->
        Sg_Let (unembed_fvar fvar, unembed_term ty, unembed_term t)

    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Unk_lid ->
        Unk

    | _ ->
        failwith "not an embedded sigelt_view"

let binders_of_env e = FStar.TypeChecker.Env.all_binders e
let type_of_binder b = match b with (b, _) -> b.sort
let term_eq = FStar.Syntax.Util.term_eq
let fresh_binder t = (gen_bv "__refl" None t, None)
let term_to_string = Print.term_to_string
