#light "off"
module FStar.Reflection.Basic

open FStar.Reflection.Data
open FStar.Syntax.Syntax
module S = FStar.Syntax.Syntax // TODO: remove, it's open

module SC = FStar.Syntax.Const
module SS = FStar.Syntax.Subst
module BU = FStar.Util
module Range = FStar.Range
module U = FStar.Syntax.Util
module Print = FStar.Syntax.Print
module Ident = FStar.Ident

//TODO:figure out why I need to annotate Data. everywhere.
// might be due to the fsproj hack

(* These file provides implementation for reflection primitives in F*.
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

let protect_embedded_term (t:typ) (x:term) =
    S.mk_Tm_app SC.fstar_refl_embed [S.iarg t; S.as_arg x] None x.pos

let un_protect_embedded_term : term -> term =
    fun (t:term) ->
        let head, args = U.head_and_args t in
        match (U.un_uinst head).n, args with
        | Tm_fvar fv, [_; (x, _)]
            when S.fv_eq_lid fv SC.fstar_refl_embed_lid ->
          x
        | _ ->
          failwith (BU.format1 "Not a protected embedded term (2): %s" (Print.term_to_string t))

let type_of_embedded : term -> typ =
    fun (t:term) ->
        let head, args = U.head_and_args t in
        match (U.un_uinst head).n, args with
        | Tm_fvar fv, [(t,_); _]
            when S.fv_eq_lid fv SC.fstar_refl_embed_lid ->
          t
        | _ ->
          failwith (BU.format1 "Not a protected embedded term (1): %s" (Print.term_to_string t))

let embed_unit (u:unit) : term = SC.exp_unit
let unembed_unit (_:term) :unit = ()

let embed_bool (b:bool) : term = if b then SC.exp_true_bool else SC.exp_false_bool
let unembed_bool (t:term) : bool =
    match (SS.compress t).n with
    | Tm_constant(FStar.Const.Const_bool b) -> b
    | _ -> failwith "Not an embedded bool"

let embed_string (s:string) : term =
    let bytes = BU.unicode_of_string s in
    S.mk (Tm_constant(FStar.Const.Const_string(bytes, Range.dummyRange)))
         None
         Range.dummyRange

let unembed_string (t:term) : string =
    let t = U.unascribe t in
    match t.n with
    | Tm_constant(FStar.Const.Const_string(bytes, _)) ->
      BU.string_of_unicode bytes
    | _ ->
      failwith ("Not an embedded string (" ^ Print.term_to_string t ^ ")")


let lid_Mktuple2 = U.mk_tuple_data_lid 2 Range.dummyRange
let lid_tuple2   = U.mk_tuple_lid 2 Range.dummyRange

let embed_binder (b:binder) : term =
    protect_embedded_term Data.fstar_refl_binder (S.bv_to_name (fst b))

let unembed_binder (t:term) : binder =
    let t = un_protect_embedded_term t in
    let t = U.unascribe t in
    match t.n with
    | Tm_name bv -> S.mk_binder bv
    | _ -> failwith "Not an embedded binder"

let rec embed_list (embed_a: ('a -> term)) (typ:term) (l:list<'a>) : term =
    match l with
    | [] -> S.mk_Tm_app (S.mk_Tm_uinst (lid_as_data_tm SC.nil_lid) [U_zero])
                        [S.iarg typ]
                        None
                        Range.dummyRange
    | hd::tl ->
            S.mk_Tm_app (S.mk_Tm_uinst (lid_as_data_tm SC.cons_lid) [U_zero])
                        [S.iarg typ;
                         S.as_arg (embed_a hd);
                         S.as_arg (embed_list embed_a typ tl)]
                        None
                        Range.dummyRange

let rec unembed_list (unembed_a: (term -> 'a)) (l:term) : list<'a> =
    let l = U.unascribe l in
    let hd, args = U.head_and_args l in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, _
        when S.fv_eq_lid fv SC.nil_lid -> []

    | Tm_fvar fv, [_t; (hd, _); (tl, _)]
        when S.fv_eq_lid fv SC.cons_lid ->
      unembed_a hd :: unembed_list unembed_a tl

    | _ ->
      failwith (BU.format1 "Not an embedded list: %s" (Print.term_to_string l))

let embed_binders l = embed_list embed_binder Data.fstar_refl_binder l
let unembed_binders t = unembed_list unembed_binder t

let embed_term (t:term) : term =
    protect_embedded_term Data.fstar_refl_term t

let unembed_term (t:term) : term =
    un_protect_embedded_term t


let embed_pair (embed_a:'a -> term) (t_a:term)
               (embed_b:'b -> term) (t_b:term)
               (x:('a * 'b)) : term =
    S.mk_Tm_app (S.mk_Tm_uinst (lid_as_data_tm lid_Mktuple2) [U_zero;U_zero])
                [S.iarg t_a;
                 S.iarg t_b;
                 S.as_arg (embed_a (fst x));
                 S.as_arg (embed_b (snd x))]
                None
                Range.dummyRange

let unembed_pair (unembed_a:term -> 'a) (unembed_b:term -> 'b) (pair:term) : ('a * 'b) =
    let pairs = U.unascribe pair in
    let hd, args = U.head_and_args pair in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_; _; (a, _); (b, _)] when S.fv_eq_lid fv lid_Mktuple2 ->
      unembed_a a, unembed_b b
    | _ -> failwith "Not an embedded pair"

let embed_option (embed_a:'a -> term) (typ:term) (o:option<'a>) : term =
    match o with
    | None ->
      S.mk_Tm_app (S.mk_Tm_uinst (lid_as_data_tm SC.none_lid) [U_zero])
                  [S.iarg typ]
                  None Range.dummyRange
    | Some a ->
      S.mk_Tm_app (S.mk_Tm_uinst (lid_as_data_tm SC.some_lid) [U_zero])
                  [S.iarg typ; S.as_arg (embed_a a)]
                  None Range.dummyRange

let unembed_option (unembed_a:term -> 'a) (o:term) : option<'a> =
   let hd, args = U.head_and_args o in
   match (U.un_uinst hd).n, args with
   | Tm_fvar fv, _ when S.fv_eq_lid fv SC.none_lid -> None
   | Tm_fvar fv, [_; (a, _)] when S.fv_eq_lid fv SC.some_lid ->
     Some (unembed_a a)
   | _ -> failwith "Not an embedded option"

let embed_fvar (fv:fv) : term =
    protect_embedded_term Data.fstar_refl_fvar (S.fv_to_tm fv)

let unembed_fvar (t:term) : fv =
    let t = un_protect_embedded_term t in
    let t = U.unascribe t in
    match t.n with
    | Tm_fvar fv -> fv
    | _ -> failwith "Not an embedded fv"

let embed_const (c:vconst) : term =
    match c with
    | C_Unit ->
        ref_C_Unit

    | C_Int s ->
        S.mk_Tm_app ref_C_Int [S.as_arg (SC.exp_int s)]
                    None Range.dummyRange

let embed_term_view (t:term_view) : term =
    match t with
    | Tv_FVar fv ->
        S.mk_Tm_app ref_Tv_FVar [S.as_arg (embed_fvar fv)]
                    None Range.dummyRange

    | Tv_Var bv ->
        S.mk_Tm_app ref_Tv_Var [S.as_arg (embed_binder bv)]
                    None Range.dummyRange

    | Tv_App (hd, a) ->
        S.mk_Tm_app ref_Tv_App [S.as_arg (embed_term hd); S.as_arg (embed_term a)]
                    None Range.dummyRange

    | Tv_Abs (b, t) ->
        S.mk_Tm_app ref_Tv_Abs [S.as_arg (embed_binder b); S.as_arg (embed_term t)]
                    None Range.dummyRange

    | Tv_Arrow (b, t) ->
        S.mk_Tm_app ref_Tv_Arrow [S.as_arg (embed_binder b); S.as_arg (embed_term t)]
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

    | Tv_Unknown ->
        ref_Tv_Unknown

let unembed_const (t:term) : vconst =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_C_Unit_lid ->
        C_Unit

    | Tm_fvar fv, [(i, _)] when S.fv_eq_lid fv ref_C_Int_lid ->
        begin match (SS.compress i).n with
        | Tm_constant (FStar.Const.Const_int (s, _)) -> C_Int s
        | _ -> failwith "unembed_const: unexpected arg for C_Int"
        end

    | _ ->
        failwith "not an embedded vconst"

let unembed_term_view (t:term) : term_view =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(b, _)] when S.fv_eq_lid fv ref_Tv_Var_lid ->
        Tv_Var (unembed_binder b)

    | Tm_fvar fv, [(b, _)] when S.fv_eq_lid fv ref_Tv_FVar_lid ->
        Tv_FVar (unembed_fvar b)

    | Tm_fvar fv, [(l, _); (r, _)] when S.fv_eq_lid fv ref_Tv_App_lid ->
        Tv_App (unembed_term l, unembed_term r)

    | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Abs_lid ->
        Tv_Abs (unembed_binder b, unembed_term t)

    | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Arrow_lid ->
        Tv_Arrow (unembed_binder b, unembed_term t)

    | Tm_fvar fv, [(u, _)] when S.fv_eq_lid fv ref_Tv_Type_lid ->
        Tv_Type (unembed_unit u)

    | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Refine_lid ->
        Tv_Refine (unembed_binder b, unembed_term t)

    | Tm_fvar fv, [(c, _)] when S.fv_eq_lid fv ref_Tv_Const_lid ->
        Tv_Const (unembed_const c)

    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Tv_Unknown_lid ->
        Tv_Unknown

    | _ ->
        failwith "not an embedded term_view"

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
    lid_as_fv (SC.p2l ns) Delta_equational None

let inspect_bv (b:binder) : string =
    Print.bv_to_string (fst b)
    // calling into Print, which really doesn't make guarantees
    // ... should be safe as we give no semantics to these names: they're just for debugging

// TODO: consider effects? probably not too useful, but something should be done
let inspect (t:term) : term_view =
    let t = U.un_uinst t in
    match t.n with
    | Tm_name bv ->
        Tv_Var (S.mk_binder bv)

    | Tm_fvar fv ->
        Tv_FVar fv

    | Tm_app (hd, []) ->
        failwith "inspect: empty arguments on Tm_app"

    | Tm_app (hd, args) ->
        // We split at the last argument, since the term_view does not
        // expose n-ary lambdas buy unary ones.
        let (a, _) = last args in
        Tv_App (S.mk_Tm_app hd (init args) None t.pos, a) // TODO: The range and tk are probably wrong. Fix

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

    | Tm_arrow (bs, k) ->
        let bs, k =  SS.open_comp bs k in
        begin match bs with
        | [] -> failwith "impossible"
        | b::bs -> Tv_Arrow (b, U.arrow bs k) // TODO: this drops the effect
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
        let c = (match c with
        | FStar.Const.Const_unit -> C_Unit
        | FStar.Const.Const_int (s, _) -> C_Int s
        | _ -> failwith (BU.format1 "unknown constant: %s" (Print.const_to_string c)))
        in
        Tv_Const c

    | _ ->
        BU.print2 "inspect: outside of expected syntax (%s, %s)\n" (Print.tag_of_term t) (Print.term_to_string t);
        Tv_Unknown

// TODO: pass in range?
let pack (tv:term_view) : term =
    match tv with
    | Tv_Var (bv, _) ->
        S.bv_to_tm bv

    | Tv_FVar fv ->
        S.fv_to_tm fv

    | Tv_App (l, r) ->
        U.mk_app l [S.as_arg r] // TODO: implicits

    | Tv_Abs (b, t) ->
        U.abs [b] t None // TODO: effect?

    | Tv_Arrow (b, t) ->
        U.arrow [b] (mk_Total t)

    | Tv_Type () ->
        U.ktype

    | Tv_Refine ((bv, _), t) ->
        U.refine bv t

    | Tv_Const (C_Unit) ->
        SC.exp_unit

    | Tv_Const (C_Int s) ->
        SC.exp_int s

    | _ ->
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

let order_binder (x:binder) (y:binder) : order =
    let n = S.order_bv (fst x) (fst y) in
    if n < 0 then Lt
    else if n = 0 then Eq
    else Gt

let is_free (x:binder) (t:term) : bool =
    BU.set_mem (fst x) (FStar.Syntax.Free.names t)

let embed_norm_step (n:norm_step) : term =
    match n with
    | Simpl ->
        ref_Simpl
    | WHNF ->
        ref_WHNF

let unembed_norm_step (t:term) : norm_step =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Simpl_lid ->
        Simpl
    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_WHNF_lid ->
        WHNF
    | _ ->
        failwith "not an embedded norm_step"
