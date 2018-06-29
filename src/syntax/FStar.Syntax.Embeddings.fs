#light "off"
module FStar.Syntax.Embeddings

open FStar
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

type norm_cb = BU.either<Ident.lid,S.term> -> S.term
let id_norm_cb : norm_cb = function
    | BU.Inr x -> x
    | BU.Inl l -> S.fv_to_tm (S.lid_as_fv l delta_equational None)
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
type printer<'a> = 'a -> string

type embedding<'a> = {
  em : 'a -> embed_t;
  un : term -> unembed_t<'a>;
  typ : typ;
  print: printer<'a>;
  emb_typ: emb_typ
}
let emb_typ_of e = e.emb_typ

let unknown_printer typ _ =
    BU.format1 "unknown %s" (Print.term_to_string typ)

let term_as_fv t =
    match (SS.compress t).n with
    | Tm_fvar fv -> fv
    | _ -> failwith (BU.format1 "Embeddings not defined for type %s" (Print.term_to_string t))

let mk_emb em un fv =
    let typ = S.fv_to_tm fv in
    {
        em = em ;
        un = un ;
        typ = typ;
        print=unknown_printer typ;
        emb_typ=ET_app (S.lid_of_fv fv |> Ident.string_of_lid, [])
    }

let mk_emb_full em un typ printer emb_typ = {
    em = em ;
    un = un ;
    typ = typ;
    print = printer;
    emb_typ = emb_typ
}

(* Eta-expand to make F# happy *)
let embed       (e:embedding<'a>) x   = e.em x
let unembed     (e:embedding<'a>) t   = e.un t
let warn_unembed (e:embedding<'a>) t n = unembed e t true n
let try_unembed  (e:embedding<'a>) t n = unembed e t false n
let type_of     (e:embedding<'a>)     = e.typ

let lazy_embed (pa:printer<'a>) (et:emb_typ) rng ta (x:'a) (f:unit -> term) =
    // BU.print3 "Embedding a %s\n\tvalue is %s\nthunked as a %s\n"
    //             (Print.term_to_string ta)
    //             (pa x)
    //             (Print.term_to_string (f()));
    if Options.eager_embedding()
    then f()
    else let thunk = FStar.Common.mk_thunk f in
         S.mk (Tm_lazy({blob=FStar.Dyn.mkdyn x;
                        ltyp=S.tun;
                        rng=rng;
                        lkind=Lazy_embedding (et, thunk)}))
               None
               rng

let rec emb_typ_to_string = function
    | ET_abstract -> "abstract"
    | ET_app (h, []) -> h
    | ET_app(h, args) -> "(" ^h^ (List.map emb_typ_to_string args |> String.concat " ")  ^")"
    | ET_fun(a, b) -> "(" ^ emb_typ_to_string a ^ "-> " ^ emb_typ_to_string b

let lazy_unembed (pa:printer<'a>) (et:emb_typ) (x:term) (ta:term) (f:term -> option<'a>) : option<'a> =
    let x = SS.compress x in
    match x.n with
    | Tm_lazy {blob=b; lkind=Lazy_embedding (et', t)}  ->
      if Options.eager_embedding()
      || et <> et'
      then f (FStar.Common.force_thunk t)
      else let a = FStar.Dyn.undyn b in
           let _ = if Options.debug_any ()
                   then BU.print1 "Unembed cancelled for %s\n"
                                (emb_typ_to_string et) in
            //BU.print4 "Unembedding a %s as a %s\n undyn a %s\n unthunked a %s\n"
           //     (Print.term_to_string tb)
           //     (Print.term_to_string ta)
           //     (pa a)
           //     (Print.term_to_string (FStar.Common.force_thunk t));
            Some a
    | _ -> f x

let mk_any_emb typ =
    let em = fun t _r _topt _norm -> t in
    let un = fun t _w _n -> Some t in
    mk_emb_full
        em
        un
        typ
        (unknown_printer typ)
        ET_abstract

let e_any =
    let em = fun t _r _topt _norm -> t in
    let un = fun t _w _n -> Some t in
    mk_emb_full
        em
        un
        S.t_term
        Print.term_to_string
        (ET_app (PC.term_lid |> Ident.string_of_lid, []))

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
    mk_emb_full
        em
        un
        S.t_unit
        (fun _ -> "()")
        (ET_app(PC.unit_lid |> Ident.string_of_lid, []))

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
    mk_emb_full
        em
        un
        S.t_bool
        BU.string_of_bool
        (ET_app(PC.bool_lid |> Ident.string_of_lid, []))

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
    mk_emb_full
        em
        un
        S.t_char
        BU.string_of_char
        (ET_app(PC.char_lid |> Ident.string_of_lid, []))

let e_int =
    let t_int = U.fvar_const PC.int_lid in
    let emb_t_int = ET_app(PC.int_lid |> Ident.string_of_lid, []) in
    let em (i:Z.t) (rng:range) _topt _norm : term =
        lazy_embed
            BigInt.string_of_big_int
            emb_t_int
            rng
            t_int
            i
            (fun () -> U.exp_int (Z.string_of_big_int i))
    in
    let un (t0:term) (w:bool) _norm : option<Z.t> =
        let t = U.unmeta_safe t0 in
        lazy_unembed
            BigInt.string_of_big_int
            emb_t_int
            t
            t_int
            (fun t ->
                match t.n with
                | Tm_constant(FStar.Const.Const_int (s, _)) ->
                    Some (Z.big_int_of_string s)
                | _ ->
                    if w then
                    Err.log_issue t0.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded int: %s" (Print.term_to_string t0)));
                    None)
    in
    mk_emb_full
        em
        un
        S.t_int
        BigInt.string_of_big_int
        emb_t_int

let e_string =
    let emb_t_string = ET_app(PC.string_lid |> Ident.string_of_lid, []) in
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
    mk_emb_full
        em
        un
        S.t_string
        (fun x -> "\"" ^ x ^ "\"")
        emb_t_string

let e_option (ea : embedding<'a>) =
    let t_option_a =
        let t_opt = U.fvar_const PC.option_lid in
        S.mk_Tm_app t_opt [S.as_arg ea.typ] None Range.dummyRange
    in
    let emb_t_option_a =
        ET_app(PC.option_lid |> Ident.string_of_lid, [ea.emb_typ])
    in
    let printer =
        (function None -> "None" | Some x -> "(Some " ^ (ea.print x) ^")")
    in
    let em (o:option<'a>) (rng:range) topt norm : term =
        lazy_embed
            printer
            emb_t_option_a
            rng
            t_option_a
            o
            (fun () ->
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
        lazy_unembed
            printer
            emb_t_option_a
            t
            t_option_a
            (fun t ->
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
    mk_emb_full
        em
        un
        (S.t_option_of (type_of ea))
        printer
        emb_t_option_a

let e_tuple2 (ea:embedding<'a>) (eb:embedding<'b>) =
    let t_pair_a_b =
        let t_tup2 = U.fvar_const PC.lid_tuple2 in
        S.mk_Tm_app t_tup2 [S.as_arg ea.typ; S.as_arg eb.typ]
                    None Range.dummyRange
    in
    let emb_t_pair_a_b =
        ET_app(PC.lid_tuple2 |> Ident.string_of_lid, [ea.emb_typ; eb.emb_typ])
    in
    let printer (x, y) =
        BU.format2 "(%s, %s)" (ea.print x) (eb.print y)
    in
    let em (x:('a * 'b)) (rng:range) topt norm : term =
        lazy_embed
            printer
            emb_t_pair_a_b
            rng
            t_pair_a_b
            x
            (fun () ->
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
        lazy_unembed
            printer
            emb_t_pair_a_b
            t
            t_pair_a_b
            (fun t ->
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
    mk_emb_full
        em
        un
        (S.t_tuple2_of (type_of ea) (type_of eb))
        printer
        emb_t_pair_a_b

let e_list (ea:embedding<'a>) =
    let t_list_a =
        let t_list = U.fvar_const PC.list_lid in
        S.mk_Tm_app t_list [S.as_arg ea.typ] None Range.dummyRange
    in
    let emb_t_list_a =
        ET_app(PC.list_lid |> Ident.string_of_lid, [ea.emb_typ])
    in
    let printer =
        (fun (l:list<'a>) -> "[" ^ (List.map ea.print l |> String.concat "; ") ^ "]")
    in
    let rec em (l:list<'a>) (rng:range) shadow_l norm : term =
        lazy_embed
            printer
            emb_t_list_a
            rng
            t_list_a
            l
            (fun () ->
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
        lazy_unembed
            printer
            emb_t_list_a
            t
            t_list_a
            (fun t ->
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
    mk_emb_full
        em
        un
        (S.t_list_of (type_of ea))
        printer
        emb_t_list_a

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
    let t_norm_step = U.fvar_const (Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step") in
    let emb_t_norm_step = ET_app (PC.norm_step_lid |> Ident.string_of_lid, []) in
    let printer _ = "norm_step" in
    let em (n:norm_step) (rng:range) _topt norm : term =
        lazy_embed
            printer
            emb_t_norm_step
            rng
            t_norm_step
            n
            (fun () ->
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
        lazy_unembed
            printer
            emb_t_norm_step
            t
            t_norm_step
            (fun t ->
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
    mk_emb_full
        em
        un
        S.t_norm_step
        printer
        emb_t_norm_step

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
    mk_emb_full
        em
        un
        S.t_range
        Range.string_of_range
        (ET_app (PC.range_lid |> Ident.string_of_lid, []))

let or_else (f: option<'a>) (g:unit -> 'a) =
    match f with
    | Some x -> x
    | None -> g ()

let e_arrow (ea:embedding<'a>) (eb:embedding<'b>) : embedding<('a -> 'b)> =
    let t_arrow =
        S.mk (Tm_arrow([S.null_bv ea.typ, None],
                        S.mk_Total eb.typ))
              None Range.dummyRange
    in
    let emb_t_arr_a_b = ET_fun(ea.emb_typ, eb.emb_typ) in
    let printer (f:'a -> 'b) = "<fun>" in
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
                | Some app -> norm (BU.Inr app))
        in
        lazy_embed
            (fun _ -> "<fun>")
            emb_t_arr_a_b
            rng
            t_arrow
            f_wrapped
            (fun () ->
                match force_shadow shadow_f with
                | None -> raise Embedding_failure //TODO: dodgy
                | Some repr_f -> norm (BU.Inr repr_f))
    in
    let un (f:term) w norm : option<('a -> 'b)> =
        lazy_unembed
            printer
            emb_t_arr_a_b
            f
            t_arrow
            (fun f ->
                let f_wrapped (a:'a) : 'b =
                    let a_tm = embed ea a f.pos None norm in
                    let b_tm = norm (BU.Inr (S.mk_Tm_app f [S.as_arg a_tm] None f.pos)) in
                    match unembed eb b_tm w norm with
                    | None -> raise Unembedding_failure
                    | Some b -> b
                in
                Some f_wrapped)
    in
    mk_emb_full
        em
        un
        t_arrow
        printer
        emb_t_arr_a_b

 /////////////////////////////////////////////////////////////////////
 //Registering top-level functions
 /////////////////////////////////////////////////////////////////////

let arrow_as_prim_step_1 (ea:embedding<'a>) (eb:embedding<'b>)
                         (f:'a -> 'b) (n_tvars:int) (fv_lid:Ident.lid) norm
   : args -> option<term> =
    let rng = Ident.range_of_lid fv_lid in
    let f_wrapped args =
        let _tvar_args, rest_args = List.splitAt n_tvars args in
        let x, _ = List.hd rest_args in //arity mismatches are handled by code that dispatches here
        let shadow_app =
            Some (FStar.Common.mk_thunk (fun () -> S.mk_Tm_app (norm (BU.Inl fv_lid)) args None rng))
        in
        match
            (BU.map_opt
                (unembed ea x true norm) (fun x ->
                 embed eb (f x) rng shadow_app norm))
        with
        | Some x -> Some x
        | None -> force_shadow shadow_app
    in
    f_wrapped

let arrow_as_prim_step_2 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>)
                         (f:'a -> 'b -> 'c) n_tvars fv_lid norm
   : args -> option<term> =
    let rng = Ident.range_of_lid fv_lid in
    let f_wrapped args =
        let _tvar_args, rest_args = List.splitAt n_tvars args in
        let x, _ = List.hd rest_args in //arity mismatches are handled by code that dispatches here
        let y, _ = List.hd (List.tl rest_args) in
        let shadow_app =
            Some (FStar.Common.mk_thunk (fun () -> S.mk_Tm_app (norm (BU.Inl fv_lid)) args None rng))
        in
        match
            (BU.bind_opt (unembed ea x true norm) (fun x ->
             BU.bind_opt (unembed eb y true norm) (fun y ->
             Some (embed ec (f x y) rng shadow_app norm))))
        with
        | Some x -> Some x
        | None -> force_shadow shadow_app
    in
    f_wrapped

let arrow_as_prim_step_3 (ea:embedding<'a>) (eb:embedding<'b>)
                         (ec:embedding<'c>) (ed:embedding<'d>)
                         (f:'a -> 'b -> 'c -> 'd) n_tvars fv_lid norm
   : args -> option<term> =
    let rng = Ident.range_of_lid fv_lid in
    let f_wrapped args =
        let _tvar_args, rest_args = List.splitAt n_tvars args in
        let x, _ = List.hd rest_args in //arity mismatches are handled by code that dispatches here
        let y, _ = List.hd (List.tl rest_args) in
        let z, _ = List.hd (List.tl (List.tl rest_args)) in
        let shadow_app =
            Some (FStar.Common.mk_thunk (fun () -> S.mk_Tm_app (norm (BU.Inl fv_lid)) args None rng))
        in
        match
            (BU.bind_opt (unembed ea x true norm) (fun x ->
             BU.bind_opt (unembed eb y true norm) (fun y ->
             BU.bind_opt (unembed ec z true norm) (fun z ->
             Some (embed ed (f x y z) rng shadow_app norm)))))
        with
        | Some x -> Some x
        | None -> force_shadow shadow_app
    in
    f_wrapped
