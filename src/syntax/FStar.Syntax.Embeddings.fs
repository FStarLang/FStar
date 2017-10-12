#light "off"
module FStar.Syntax.Embeddings

open FStar.All
open FStar.Syntax.Syntax
module Print = FStar.Syntax.Print
module S = FStar.Syntax.Syntax
module C = FStar.Const
module PC = FStar.Parser.Const
module SS = FStar.Syntax.Subst
module BU = FStar.Util
module Range = FStar.Range
module U = FStar.Syntax.Util
module UF = FStar.Syntax.Unionfind
module Ident = FStar.Ident
module Err = FStar.Errors

// embed: turning a value into a term (compiler internals -> userland)
// unembed: interpreting a term as a value, which might fail (userland -> compiler internals)

let embed_unit (u:unit) : term = U.exp_unit
let unembed_unit (t:term) : option<unit> =
    let t = U.unascribe t in
    match t.n with
    | S.Tm_constant C.Const_unit -> Some ()
    | _ -> None

let embed_bool (b:bool) : term = if b then U.exp_true_bool else U.exp_false_bool
let unembed_bool (t:term) : option<bool> =
    match (SS.compress (U.unmeta t)).n with
    | Tm_constant(FStar.Const.Const_bool b) -> Some b
    | _ ->
        Err.warn t.pos (BU.format1 "Not an embedded bool: %s" (Print.term_to_string t));
        None

let embed_int (i:int) : term = U.exp_int (BU.string_of_int i)
let unembed_int (t:term) : option<int> =
    // What's the portable solution? Let's do this for now
    match (SS.compress (U.unmeta t)).n with
    | Tm_constant(FStar.Const.Const_int (s, _)) ->
        Some (BU.int_of_string s)
    | _ ->
        Err.warn t.pos (BU.format1 "Not an embedded int: %s" (Print.term_to_string t));
        None

let embed_string (s:string) : term =
    S.mk (Tm_constant(FStar.Const.Const_string(s, Range.dummyRange)))
         None
         Range.dummyRange

let unembed_string (t:term) : option<string> =
    let t = U.unmeta t in
    match t.n with
    | Tm_constant(FStar.Const.Const_string(s, _)) -> Some s
    | _ ->
        Err.warn t.pos (BU.format1 "Not an embedded string: %s" (Print.term_to_string t));
        None

let embed_pair (embed_a:'a -> term) (t_a:term)
               (embed_b:'b -> term) (t_b:term)
               (x:('a * 'b)) : term =
    S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.lid_Mktuple2) [U_zero;U_zero])
                [S.iarg t_a;
                 S.iarg t_b;
                 S.as_arg (embed_a (fst x));
                 S.as_arg (embed_b (snd x))]
                None
                Range.dummyRange

let unembed_pair (unembed_a:term -> option<'a>) (unembed_b:term -> option<'b>) (t:term) : option<('a * 'b)> =
    let t = U.unmeta t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_; _; (a, _); (b, _)] when S.fv_eq_lid fv PC.lid_Mktuple2 ->
        BU.bind_opt (unembed_a a) (fun a ->
        BU.bind_opt (unembed_b b) (fun b ->
        Some (a, b)))
    | _ ->
        Err.warn t.pos (BU.format1 "Not an embedded pair: %s" (Print.term_to_string t));
        None

let embed_option (embed_a:'a -> term) (typ:term) (o:option<'a>) : term =
    match o with
    | None ->
      S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.none_lid) [U_zero])
                  [S.iarg typ]
                  None Range.dummyRange
    | Some a ->
      S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.some_lid) [U_zero])
                  [S.iarg typ; S.as_arg (embed_a a)]
                  None Range.dummyRange

let unembed_option (unembed_a:term -> option<'a>) (t:term) : option<option<'a>> =
   let hd, args = U.head_and_args (U.unmeta t) in
   match (U.un_uinst hd).n, args with
   | Tm_fvar fv, _ when S.fv_eq_lid fv PC.none_lid -> Some None
   | Tm_fvar fv, [_; (a, _)] when S.fv_eq_lid fv PC.some_lid ->
        BU.bind_opt (unembed_a a) (fun a -> Some (Some a))
   | _ ->
        Err.warn t.pos (BU.format1 "Not an embedded option: %s" (Print.term_to_string t));
        None

let rec embed_list (embed_a: ('a -> term)) (typ:term) (l:list<'a>) : term =
    match l with
    | [] -> S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.nil_lid) [U_zero])
                        [S.iarg typ]
                        None
                        Range.dummyRange
    | hd::tl ->
            S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.cons_lid) [U_zero])
                        [S.iarg typ;
                         S.as_arg (embed_a hd);
                         S.as_arg (embed_list embed_a typ tl)]
                        None
                        Range.dummyRange

let rec unembed_list (unembed_a: term -> option<'a>) (t:term) : option<list<'a>> =
    let t = U.unmeta t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, _
        when S.fv_eq_lid fv PC.nil_lid -> Some []

    | Tm_fvar fv, [_t; (hd, _); (tl, _)]
        when S.fv_eq_lid fv PC.cons_lid ->
        BU.bind_opt (unembed_a hd) (fun hd ->
        BU.bind_opt (unembed_list unembed_a tl) (fun tl ->
        Some (hd :: tl)))
    | _ ->
        Err.warn t.pos (BU.format1 "Not an embedded list: %s" (Print.term_to_string t));
        None

let embed_string_list ss = embed_list embed_string S.t_string ss
let unembed_string_list t = unembed_list unembed_string t

type norm_step =
    | Simpl
    | WHNF
    | Primops
    | Delta
    | Zeta
    | Iota
    | UnfoldOnly of list<string>

(* the steps as terms *)
let steps_Simpl      = tdataconstr PC.steps_simpl
let steps_WHNF       = tdataconstr PC.steps_whnf
let steps_Primops    = tdataconstr PC.steps_primops
let steps_Delta      = tdataconstr PC.steps_delta
let steps_Zeta       = tdataconstr PC.steps_zeta
let steps_Iota       = tdataconstr PC.steps_iota
let steps_UnfoldOnly = tdataconstr PC.steps_unfoldonly

let embed_norm_step (n:norm_step) : term =
    match n with
    | Simpl ->
        steps_Simpl
    | WHNF ->
        steps_WHNF
    | Primops ->
        steps_Primops
    | Delta ->
        steps_Delta
    | Zeta ->
        steps_Zeta
    | Iota ->
        steps_Iota
    | UnfoldOnly l ->
        S.mk_Tm_app steps_UnfoldOnly [S.as_arg (embed_list embed_string S.t_string l)]
                    None Range.dummyRange

let unembed_norm_step (t:term) : option<norm_step> =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_simpl ->
        Some Simpl
    | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_whnf ->
        Some WHNF
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
        Err.warn t.pos (BU.format1 "Not an embedded norm_step: %s" (Print.term_to_string t));
        None

let embed_range (r:Range.range) : term =
    S.mk (Tm_constant (C.Const_range r)) None r

let unembed_range (t:term) : option<Range.range> =
    match t.n with
    | Tm_constant (C.Const_range r) -> Some r
    | _ ->
        Err.warn t.pos (BU.format1 "Not an embedded range: %s" (Print.term_to_string t));
        None
