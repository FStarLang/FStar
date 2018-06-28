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

type norm_cb = S.term -> S.term
exception Embedding_failure
exception Unembedding_failure
type shadow_term = option<FStar.Common.thunk<term>>

let map_shadow (s:shadow_term) (f:term -> term) : shadow_term =
    BU.map_opt s (fun s ->
    FStar.Common.mk_thunk (fun () -> f (FStar.Common.force_thunk s)))
let force_shadow (s:shadow_term) = BU.map_opt s FStar.Common.force_thunk

type embed_t = FStar.Range.range -> shadow_term -> norm_cb -> term
type unembed_t<'a> = bool -> norm_cb -> option<'a> // bool = whether we

type raw_embedder<'a>   = 'a -> embed_t
type raw_unembedder<'a> = term -> unembed_t<'a>

type embedding<'a> = {
  em : 'a -> embed_t;
  un : term -> unembed_t<'a>;
  typ : typ
}
let mk_emb em un typ = { em = em ; un = un ; typ = typ }

(* Eta-expand to make F# happy *)
let embed       (e:embedding<'a>) x   = e.em x
let unembed     (e:embedding<'a>) t   = e.un t
let warn_unembed (e:embedding<'a>) t n = unembed e t true n
let try_unembed  (e:embedding<'a>) t n = unembed e t false n
let type_of     (e:embedding<'a>)     = e.typ

let lazy_embed rng (x:'a) (f:unit -> term) =
    S.mk (Tm_lazy({blob=FStar.Dyn.mkdyn x;
                   typ=S.tun;
                   rng=rng;
                   lkind=Lazy_embedding (FStar.Common.mk_thunk f)}))
         None
         rng

let lazy_unembed (x:term) (f:term -> option<'a>) : option<'a> =
    let x = SS.compress x in
    match x.n with
    | Tm_lazy {blob=b; lkind=Lazy_embedding _} -> Some (FStar.Dyn.undyn b)
    | _ -> f x

let e_any =
    let em = fun t _r _topt _norm -> t in
    let un = fun t _w _n -> Some t in
    let typ = S.t_term in
    mk_emb em un typ

let mk_any_emb typ = { em = e_any.em ; un = e_any.un ; typ = typ }

let e_unit =
    let em (u:unit) rng _topt _norm : term = { U.exp_unit with pos = rng } in
    let un (t0:term) (w:bool) _norm : option<unit> =
        let t = U.unascribe t0 in
        match t.n with
        | S.Tm_constant C.Const_unit -> Some ()
        | _ ->
            if w then
            Err.log_issue t0.pos (Err.Warning_NotEmbedded, BU.format1 "Not an embedded unit: %s" (Print.term_to_string t));
            None
    in
    mk_emb em un S.t_unit

let e_bool =
    let em (b:bool) rng _topt _norm : term =
        let t = if b then U.exp_true_bool else U.exp_false_bool in
        { t with pos = rng }
    in
    let un (t0:term) (w:bool) _norm : option<bool> =
        let t = U.unmeta_safe t0 in
        match t.n with
        | Tm_constant(FStar.Const.Const_bool b) -> Some b
        | _ ->
            if w then
            Err.log_issue t0.pos (Err.Warning_NotEmbedded, BU.format1 "Not an embedded bool: %s" (Print.term_to_string t0));
            None
    in
    mk_emb em un S.t_bool

let e_char =
    let em (c:char) (rng:range) _topt _norm : term =
        let t = U.exp_char c in
        { t with pos = rng }
    in
    let un (t0:term) (w:bool) _norm : option<char> =
        let t = U.unmeta_safe t0 in
        match t.n with
        | Tm_constant(FStar.Const.Const_char c) -> Some c
        | _ ->
            if w then
            Err.log_issue t0.pos (Err.Warning_NotEmbedded, BU.format1 "Not an embedded char: %s" (Print.term_to_string t0));
            None
    in
    mk_emb em un S.t_char

let e_int =
    let em (i:Z.t) (rng:range) _topt _norm : term =
        lazy_embed rng i (fun () -> U.exp_int (Z.string_of_big_int i))
    in
    let un (t0:term) (w:bool) _norm : option<Z.t> =
        let t = U.unmeta_safe t0 in
        lazy_unembed t (fun t ->
            match t.n with
            | Tm_constant(FStar.Const.Const_int (s, _)) ->
                Some (Z.big_int_of_string s)
            | _ ->
                if w then
                Err.log_issue t0.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded int: %s" (Print.term_to_string t0)));
                None)
    in
    mk_emb em un S.t_int

let e_string =
    let em (s:string) (rng:range) _topt _norm : term =
        S.mk (Tm_constant(FStar.Const.Const_string(s, rng)))
             None
             rng
    in
    let un (t0:term) (w:bool) _norm : option<string> =
        let t = U.unmeta_safe t0 in
        match t.n with
        | Tm_constant(FStar.Const.Const_string(s, _)) -> Some s
        | _ ->
            if w then
            Err.log_issue t0.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded string: %s" (Print.term_to_string t0)));
            None
    in
    mk_emb em un S.t_string

let e_option (ea : embedding<'a>) =
    let em (o:option<'a>) (rng:range) topt norm : term =
        lazy_embed rng o (fun () ->
        match o with
        | None ->
          S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.none_lid) [U_zero])
                      [S.iarg (type_of ea)]
                      None rng
        | Some a ->
          let shadow_a = map_shadow topt (fun t ->
            let v = Ident.mk_ident ("v", rng) in
            let some_v = U.mk_field_projector_name_from_ident PC.some_lid v in
            let some_v_tm = S.fv_to_tm (lid_as_fv some_v delta_equational None) in
            S.mk_Tm_app (S.mk_Tm_uinst some_v_tm [U_zero])
                        [S.iarg (type_of ea); S.as_arg t]
                        None
                        rng)
          in
          S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.some_lid) [U_zero])
                      [S.iarg (type_of ea); S.as_arg (embed ea a rng shadow_a norm)]
                      None rng)
    in
    let un (t0:term) (w:bool) norm : option<option<'a>> =
        let t = U.unmeta_safe t0 in
        lazy_unembed t (fun t ->
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, _ when S.fv_eq_lid fv PC.none_lid -> Some None
        | Tm_fvar fv, [_; (a, _)] when S.fv_eq_lid fv PC.some_lid ->
             BU.bind_opt (unembed ea a w norm) (fun a -> Some (Some a))
        | _ ->
             if w then
             Err.log_issue t0.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded option: %s" (Print.term_to_string t0)));
             None)
    in
    mk_emb em un (S.t_option_of (type_of ea))

let e_tuple2 (ea:embedding<'a>) (eb:embedding<'b>) =
    let em (x:('a * 'b)) (rng:range) topt norm : term =
        lazy_embed rng x (fun () ->
        let proj i ab =
            let proj_1, _ = U.mk_field_projector_name (PC.mk_tuple_data_lid 2 rng) (S.null_bv S.tun) i in
            let proj_1_tm = S.fv_to_tm (lid_as_fv proj_1 delta_equational None) in
            S.mk_Tm_app (S.mk_Tm_uinst proj_1_tm [U_zero])
                        [S.iarg (type_of ea);
                         S.iarg (type_of eb);
                         S.as_arg ab]
                        None
                        rng
        in
        let shadow_a = map_shadow topt (proj 1) in
        let shadow_b = map_shadow topt (proj 2) in
        S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.lid_Mktuple2) [U_zero;U_zero])
                    [S.iarg (type_of ea);
                     S.iarg (type_of eb);
                     S.as_arg (embed ea (fst x) rng shadow_a norm);
                     S.as_arg (embed eb (snd x) rng shadow_b norm)]
                    None
                    rng)
    in
    let un (t0:term) (w:bool) norm : option<('a * 'b)> =
        let t = U.unmeta_safe t0 in
        lazy_unembed t (fun t ->
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [_; _; (a, _); (b, _)] when S.fv_eq_lid fv PC.lid_Mktuple2 ->
            BU.bind_opt (unembed ea a w norm) (fun a ->
            BU.bind_opt (unembed eb b w norm) (fun b ->
            Some (a, b)))
        | _ ->
            if w then
            Err.log_issue t0.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded pair: %s" (Print.term_to_string t0)));
            None)
    in
    mk_emb em un (S.t_tuple2_of (type_of ea) (type_of eb))

let e_list (ea:embedding<'a>) =
    let rec em (l:list<'a>) (rng:range) shadow_l norm : term =
        lazy_embed rng l (fun () ->
        let t = S.iarg (type_of ea) in
        match l with
        | [] ->
          S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.nil_lid) [U_zero]) //NS: the universe here is bogus
                      [t]
                      None
                      rng
        | hd::tl ->
          let cons =
              S.mk_Tm_uinst (S.tdataconstr PC.cons_lid) [U_zero]
          in
          let proj f cons_tm =
            let fid = Ident.mk_ident (f, rng) in
            let proj = U.mk_field_projector_name_from_ident PC.cons_lid fid in
            let proj_tm = S.fv_to_tm (lid_as_fv proj delta_equational None) in
            S.mk_Tm_app (S.mk_Tm_uinst proj_tm [U_zero])
                        [S.iarg (type_of ea);
                         S.as_arg cons_tm]
                        None
                        rng
          in
          let shadow_hd = map_shadow shadow_l (proj "hd") in
          let shadow_tl = map_shadow shadow_l (proj "tl") in
          S.mk_Tm_app cons
                      [t;
                       S.as_arg (embed ea hd rng shadow_hd norm);
                       S.as_arg (em tl rng shadow_tl norm)]
                      None
                      rng)
    in
    let rec un (t0:term) (w:bool) norm : option<list<'a>> =
        let t = U.unmeta_safe t0 in
        lazy_unembed t (fun t ->
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, _
            when S.fv_eq_lid fv PC.nil_lid -> Some []

        | Tm_fvar fv, [(_, Some (Implicit _)); (hd, None); (tl, None)]
        | Tm_fvar fv, [(hd, None); (tl, None)]
            when S.fv_eq_lid fv PC.cons_lid ->
            BU.bind_opt (unembed ea hd w norm) (fun hd ->
            BU.bind_opt (un tl w norm) (fun tl ->
            Some (hd :: tl)))
        | _ ->
            if w then
            Err.log_issue t0.pos (Err.Warning_NotEmbedded, BU.format1 "Not an embedded list: %s" (Print.term_to_string t0));
            None)
    in
    mk_emb em un (S.t_list_of (type_of ea))

let e_string_list = e_list e_string

type norm_step =
    | Simpl
    | Weak
    | HNF
    | Primops
    | Delta
    | Zeta
    | Iota
    | UnfoldOnly of list<string>
    | UnfoldFully of list<string>
    | UnfoldAttr of attribute

(* the steps as terms *)
let steps_Simpl         = tdataconstr PC.steps_simpl
let steps_Weak          = tdataconstr PC.steps_weak
let steps_HNF           = tdataconstr PC.steps_hnf
let steps_Primops       = tdataconstr PC.steps_primops
let steps_Delta         = tdataconstr PC.steps_delta
let steps_Zeta          = tdataconstr PC.steps_zeta
let steps_Iota          = tdataconstr PC.steps_iota
let steps_UnfoldOnly    = tdataconstr PC.steps_unfoldonly
let steps_UnfoldFully   = tdataconstr PC.steps_unfoldonly
let steps_UnfoldAttr    = tdataconstr PC.steps_unfoldattr

let e_norm_step =
    let em (n:norm_step) (rng:range) _topt norm : term =
        lazy_embed rng n (fun () ->
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
            S.mk_Tm_app steps_UnfoldOnly [S.as_arg (embed (e_list e_string) l rng None norm)]
                        None rng
        | UnfoldFully l ->
            S.mk_Tm_app steps_UnfoldFully [S.as_arg (embed (e_list e_string) l rng None norm)]
                        None rng
        | UnfoldAttr a ->
            S.mk_Tm_app steps_UnfoldAttr [S.as_arg a] None rng)
    in
    let un (t0:term) (w:bool) norm : option<norm_step> =
        let t = U.unmeta_safe t0 in
        lazy_unembed t (fun t ->
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
            BU.bind_opt (unembed (e_list e_string) l w norm) (fun ss ->
            Some <| UnfoldOnly ss)
        | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldfully ->
            BU.bind_opt (unembed (e_list e_string) l w norm) (fun ss ->
            Some <| UnfoldFully ss)
        | Tm_fvar fv, [_;(a, _)] when S.fv_eq_lid fv PC.steps_unfoldattr ->
            Some (UnfoldAttr a)
        | _ ->
            if w then
            Err.log_issue t0.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded norm_step: %s" (Print.term_to_string t0)));
            None)
    in
    mk_emb em un S.t_norm_step


let e_range =
    let em (r:range) (rng:range) _shadow _norm : term =
        S.mk (Tm_constant (C.Const_range r)) None rng
    in
    let un (t0:term) (w:bool) _norm : option<range> =
        let t = U.unmeta_safe t0 in
        match t.n with
        | Tm_constant (C.Const_range r) -> Some r
        | _ ->
            if w then
            Err.log_issue t0.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded range: %s" (Print.term_to_string t0)));
            None
    in
    mk_emb em un S.t_range

let or_else (f: option<'a>) (g:unit -> 'a) =
    match f with
    | Some x -> x
    | None -> g ()

let embed_arrow_1 (ea:embedding<'a>) (eb:embedding<'b>) =
    let em (f:'a -> 'b) rng shadow_f norm =
        let f_wrapped (x:term) =
            let shadow_app = map_shadow shadow_f (fun f ->
                S.mk_Tm_app f [S.as_arg x] None rng)
            in
            or_else
            (BU.map_opt (unembed ea x true norm) (fun x ->
                embed eb (f x) rng shadow_app norm))
            (fun () ->
                match force_shadow shadow_app with
                | None -> raise Embedding_failure
                | Some app -> norm app)
        in
        lazy_embed rng f_wrapped (fun () ->
        match force_shadow shadow_f with
        | None -> raise Embedding_failure //TODO: dodgy
        | Some repr_f -> norm repr_f)
    in
    let un (f:term) w norm =
        let f_wrapped (a:'a) =
            let a_tm = embed ea a f.pos None norm in
            let b_tm = norm (S.mk_Tm_app f [S.as_arg a_tm] None f.pos) in
            match unembed eb b_tm w norm with
            | None -> raise Unembedding_failure
            | Some b -> b
        in
        Some f_wrapped
    in
    let tarr =
        S.mk (Tm_arrow ([S.mk_binder (S.new_bv None (type_of ea))],
                        S.mk_Total <| type_of eb))
              None
              FStar.Range.dummyRange
    in
    mk_emb em un tarr