#light "off"
module FStar.Syntax.Embeddings

open FStar.All
open FStar.Syntax.Syntax
open FStar.Range

module Print = FStar.Syntax.Print
module S = FStar.Syntax.Syntax
module C = FStar.Const
module PC = FStar.Parser.Const
module SS = FStar.Syntax.Subst
module BU = FStar.Util
module U = FStar.Syntax.Util
module UF = FStar.Syntax.Unionfind
module Ident = FStar.Ident
module Err = FStar.Errors
module Z = FStar.BigInt
open FStar.Char

type embedder<'a>   = range -> 'a -> term
type unembedder<'a> = term -> option<'a>

// embed: turning a value into a term (compiler internals -> userland)
// unembed: interpreting a term as a value, which might fail (userland -> compiler internals)

let embed_unit (rng:range) (u:unit) : term = { U.exp_unit with pos = rng }
let __unembed_unit (w:bool) (t0:term) : option<unit> =
    let t = U.unascribe t0 in
    match t.n with
    | S.Tm_constant C.Const_unit -> Some ()
    | _ ->
        if w then
        Err.warn t0.pos (BU.format1 "Not an embedded unit: %s" (Print.term_to_string t));
        None

(* These two, and every other unembedder, need to be eta-expanded
 * because F# is stupid about this *)
let unembed_unit      t = __unembed_unit true  t
let unembed_unit_safe t = __unembed_unit false t

let embed_bool (rng:range) (b:bool) : term =
    let t = if b then U.exp_true_bool else U.exp_false_bool in
    { t with pos = rng }

let __unembed_bool (w:bool) (t0:term) : option<bool> =
    let t = U.unmeta_safe t0 in
    match t.n with
    | Tm_constant(FStar.Const.Const_bool b) -> Some b
    | _ ->
        if w then
        Err.warn t0.pos (BU.format1 "Not an embedded bool: %s" (Print.term_to_string t0));
        None

let unembed_bool      t = __unembed_bool true  t
let unembed_bool_safe t = __unembed_bool false t

let embed_char (rng:range) (c:char) : term =
    let t = U.exp_char c in
    { t with pos = rng }

let __unembed_char (w:bool) (t0:term) : option<char> =
    let t = U.unmeta_safe t0 in
    match t.n with
    | Tm_constant(FStar.Const.Const_char c) -> Some c
    | _ ->
        if w then
        Err.warn t0.pos (BU.format1 "Not an embedded char: %s" (Print.term_to_string t0));
        None

let unembed_char      t = __unembed_char true  t
let unembed_char_safe t = __unembed_char false t

let embed_int (rng:range) (i:Z.t) : term =
    let t = U.exp_int (Z.string_of_big_int i) in
    { t with pos = rng }

let __unembed_int (w:bool) (t0:term) : option<Z.t> =
    let t = U.unmeta_safe t0 in
    match t.n with
    | Tm_constant(FStar.Const.Const_int (s, _)) ->
        Some (Z.big_int_of_string s)
    | _ ->
        if w then
        Err.warn t0.pos (BU.format1 "Not an embedded int: %s" (Print.term_to_string t0));
        None

let unembed_int      t = __unembed_int true  t
let unembed_int_safe t = __unembed_int false t

let embed_string (rng:range) (s:string) : term =
    S.mk (Tm_constant(FStar.Const.Const_string(s, rng)))
         None
         rng

let __unembed_string (w:bool) (t0:term) : option<string> =
    let t = U.unmeta_safe t0 in
    match t.n with
    | Tm_constant(FStar.Const.Const_string(s, _)) -> Some s
    | _ ->
        if w then
        Err.warn t0.pos (BU.format1 "Not an embedded string: %s" (Print.term_to_string t0));
        None

let unembed_string      t = __unembed_string true  t
let unembed_string_safe t = __unembed_string false t

let embed_pair (embed_a:embedder<'a>) (t_a:term)
               (embed_b:embedder<'b>) (t_b:term)
               (rng:range) (x:('a * 'b)) : term =
    S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.lid_Mktuple2) [U_zero;U_zero])
                [S.iarg t_a;
                 S.iarg t_b;
                 S.as_arg (embed_a rng (fst x));
                 S.as_arg (embed_b rng (snd x))]
                None
                rng

let __unembed_pair (w:bool)
                   (unembed_a:unembedder<'a>)
                   (unembed_b:unembedder<'b>)
                   (t0:term) : option<('a * 'b)> =
    let t = U.unmeta_safe t0 in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_; _; (a, _); (b, _)] when S.fv_eq_lid fv PC.lid_Mktuple2 ->
        BU.bind_opt (unembed_a a) (fun a ->
        BU.bind_opt (unembed_b b) (fun b ->
        Some (a, b)))
    | _ ->
        if w then
        Err.warn t0.pos (BU.format1 "Not an embedded pair: %s" (Print.term_to_string t0));
        None

let unembed_pair      ul ur t = __unembed_pair true  ul ur t
let unembed_pair_safe ul ur t = __unembed_pair false ul ur t

let embed_option (embed_a:embedder<'a>) (typ:term) (rng:range) (o:option<'a>) : term =
    match o with
    | None ->
      S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.none_lid) [U_zero])
                  [S.iarg typ]
                  None rng
    | Some a ->
      S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.some_lid) [U_zero])
                  [S.iarg typ; S.as_arg (embed_a rng a)]
                  None rng

let __unembed_option (w:bool) (unembed_a:unembedder<'a>) (t0:term) : option<option<'a>> =
    let t = U.unmeta_safe t0 in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, _ when S.fv_eq_lid fv PC.none_lid -> Some None
    | Tm_fvar fv, [_; (a, _)] when S.fv_eq_lid fv PC.some_lid ->
         BU.bind_opt (unembed_a a) (fun a -> Some (Some a))
    | _ ->
         if w then
         Err.warn t0.pos (BU.format1 "Not an embedded option: %s" (Print.term_to_string t0));
         None

let unembed_option      ua t = __unembed_option true  ua t
let unembed_option_safe ua t = __unembed_option false ua t

let rec embed_list (embed_a:embedder<'a>) (typ:term) (rng:range) (l:list<'a>) : term =
    match l with
    | [] -> S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.nil_lid) [U_zero])
                        [S.iarg typ]
                        None
                        rng
    | hd::tl ->
            S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.cons_lid) [U_zero])
                        [S.iarg typ;
                         S.as_arg (embed_a rng hd);
                         S.as_arg (embed_list embed_a typ rng tl)]
                        None
                        rng

let rec __unembed_list (w:bool) (unembed_a: unembedder<'a>) (t0:term) : option<list<'a>> =
    let t = U.unmeta_safe t0 in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, _
        when S.fv_eq_lid fv PC.nil_lid -> Some []

    | Tm_fvar fv, [_t; (hd, _); (tl, _)]
        when S.fv_eq_lid fv PC.cons_lid ->
        BU.bind_opt (unembed_a hd) (fun hd ->
        BU.bind_opt (__unembed_list w unembed_a tl) (fun tl ->
        Some (hd :: tl)))
    | _ ->
        if w then
        Err.warn t0.pos (BU.format1 "Not an embedded list: %s" (Print.term_to_string t0));
        None

let unembed_list      ua t = __unembed_list true  ua t
let unembed_list_safe ua t = __unembed_list false ua t

// Commonly called
let embed_string_list rng ss   = embed_list embed_string S.t_string rng ss
let unembed_string_list      t = unembed_list unembed_string t
let unembed_string_list_safe t = unembed_list_safe unembed_string_safe t

type norm_step =
    | Simpl
    | Weak
    | HNF
    | Primops
    | Delta
    | Zeta
    | Iota
    | UnfoldOnly of list<string>

(* the steps as terms *)
let steps_Simpl      = tdataconstr PC.steps_simpl
let steps_Weak       = tdataconstr PC.steps_weak
let steps_HNF        = tdataconstr PC.steps_hnf
let steps_Primops    = tdataconstr PC.steps_primops
let steps_Delta      = tdataconstr PC.steps_delta
let steps_Zeta       = tdataconstr PC.steps_zeta
let steps_Iota       = tdataconstr PC.steps_iota
let steps_UnfoldOnly = tdataconstr PC.steps_unfoldonly

let embed_norm_step (rng:range) (n:norm_step) : term =
    match n with
    | Simpl ->
        steps_Simpl
    | Weak ->
        steps_Weak
    | HNF ->
        steps_HNF
    | Primops ->
        steps_Primops
    | Delta ->
        steps_Delta
    | Zeta ->
        steps_Zeta
    | Iota ->
        steps_Iota
    | UnfoldOnly l ->
        S.mk_Tm_app steps_UnfoldOnly [S.as_arg (embed_list embed_string S.t_string rng l)]
                    None rng

let __unembed_norm_step (w:bool) (t0:term) : option<norm_step> =
    let t = U.unmeta_safe t0 in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_simpl ->
        Some Simpl
    | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_weak ->
        Some Weak
    | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_hnf ->
        Some HNF
    | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_primops ->
        Some Primops
    | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_delta ->
        Some Delta
    | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_zeta ->
        Some Zeta
    | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_iota ->
        Some Iota
    | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldonly ->
        BU.bind_opt (unembed_list unembed_string l) (fun ss ->
        Some <| UnfoldOnly ss)
    | _ ->
        if w then
        Err.warn t0.pos (BU.format1 "Not an embedded norm_step: %s" (Print.term_to_string t0));
        None

let unembed_norm_step      t = __unembed_norm_step true  t
let unembed_norm_step_safe t = __unembed_norm_step false t

let embed_range (rng:range) (r:range) : term =
    S.mk (Tm_constant (C.Const_range r)) None rng

let __unembed_range (w:bool) (t0:term) : option<range> =
    let t = U.unmeta_safe t0 in
    match t.n with
    | Tm_constant (C.Const_range r) -> Some r
    | _ ->
        if w then
        Err.warn t0.pos (BU.format1 "Not an embedded range: %s" (Print.term_to_string t0));
        None

let unembed_range      t = __unembed_range true  t
let unembed_range_safe t = __unembed_range false t
