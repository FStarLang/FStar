#light "off"
module FStar.Syntax.Embeddings

open FStar
open FStar.Pervasives
open FStar.All
open FStar.Syntax.Syntax
open FStar.Range
open FStar.VConfig

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

type norm_cb = either<Ident.lid,S.term> -> S.term
let id_norm_cb : norm_cb = function
    | Inr x -> x
    | Inl l -> S.fv_to_tm (S.lid_as_fv l delta_equational None)
exception Embedding_failure
exception Unembedding_failure
type shadow_term = option<Thunk.t<term>>

let map_shadow (s:shadow_term) (f:term -> term) : shadow_term =
    BU.map_opt s (Thunk.map f)
let force_shadow (s:shadow_term) = BU.map_opt s Thunk.force

type embed_t = FStar.Range.range -> shadow_term -> norm_cb -> term
type unembed_t<'a> = bool -> norm_cb -> option<'a> // bool = whether we expect success, and should warn if unembedding fails

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
let embed        (e:embedding<'a>) x   = e.em x
let unembed      (e:embedding<'a>) t   = e.un t
let warn_unembed (e:embedding<'a>) t n = unembed e t true n
let try_unembed  (e:embedding<'a>) t n = unembed e t false n
let type_of      (e:embedding<'a>)     = e.typ
let set_type ty  (e:embedding<'a>)     = { e with typ = ty }

let embed_as (ea:embedding<'a>) (ab : 'a -> 'b) (ba : 'b -> 'a) (o:option<typ>) =
    mk_emb_full (fun (x:'b) -> embed ea (ba x))
                (fun (t:term) w cb -> BU.map_opt (unembed ea t w cb) ab)
                (match o with | Some t -> t | _ -> type_of ea)
                (fun (x:'b) -> BU.format1 "(embed_as>> %s)\n" (ea.print (ba x)))
                ea.emb_typ

let lazy_embed (pa:printer<'a>) (et:emb_typ) rng ta (x:'a) (f:unit -> term) =
    if !Options.debug_embedding
    then BU.print3 "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                         (Print.term_to_string ta)
                         (Print.emb_typ_to_string et)
                         (pa x);
    if !Options.eager_embedding
    then f()
    else let thunk = Thunk.mk f in
         U.mk_lazy x S.tun (Lazy_embedding (et, thunk)) (Some rng)

let lazy_unembed (pa:printer<'a>) (et:emb_typ) (x:term) (ta:term) (f:term -> option<'a>) : option<'a> =
    let x = SS.compress x in
    match x.n with
    | Tm_lazy {blob=b; lkind=Lazy_embedding (et', t)}  ->
      if et <> et'
      || !Options.eager_embedding
      then let res = f (Thunk.force t) in
           let _ = if !Options.debug_embedding
                   then BU.print3 "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                                (Print.emb_typ_to_string et)
                                (Print.emb_typ_to_string et')
                                (match res with None -> "None" | Some x -> "Some " ^ (pa x))
           in
           res
      else let a = FStar.Dyn.undyn b in
           let _ = if !Options.debug_embedding
                   then BU.print2 "Unembed cancelled for %s\n\tvalue is %s\n"
                                (Print.emb_typ_to_string et)
                                  (pa a)
           in
           Some a
    | _ ->
      let aopt = f x in
      let _ = if !Options.debug_embedding
              then BU.print3 "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                               (Print.emb_typ_to_string et)
                               (Print.term_to_string x)
                               (match aopt with None -> "None" | Some a -> "Some " ^ pa a) in
      aopt


let mk_any_emb typ =
    let em = fun t _r _topt _norm ->
      if !Options.debug_embedding
      then BU.print1 "Embedding abstract: %s\n" (unknown_printer typ t);
      t
    in
    let un = fun t _w _n ->
      if !Options.debug_embedding
      then BU.print1 "Unembedding abstract: %s\n" (unknown_printer typ t);
      Some t
    in
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

let e_fsint = embed_as e_int Z.to_int_fs Z.of_int_fs None

let e_string =
    let emb_t_string = ET_app(PC.string_lid |> Ident.string_of_lid, []) in
    let em (s:string) (rng:range) _topt _norm : term =
        S.mk (Tm_constant(FStar.Const.Const_string(s, rng)))
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
        S.mk_Tm_app t_opt [S.as_arg ea.typ] Range.dummyRange
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
                              rng
                | Some a ->
                  let shadow_a = map_shadow topt (fun t ->
                    let v = Ident.mk_ident ("v", rng) in
                    let some_v = U.mk_field_projector_name_from_ident PC.some_lid v in
                    let some_v_tm = S.fv_to_tm (lid_as_fv some_v delta_equational None) in
                    S.mk_Tm_app (S.mk_Tm_uinst some_v_tm [U_zero])
                                [S.iarg (type_of ea); S.as_arg t]
                                rng)
                  in
                  S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.some_lid) [U_zero])
                              [S.iarg (type_of ea); S.as_arg (embed ea a rng shadow_a norm)]
                              rng)
    in
    let un (t0:term) (w:bool) norm : option<option<'a>> =
        let t = U.unmeta_safe t0 in
        lazy_unembed
            printer
            emb_t_option_a
            t
            t_option_a
            (fun t ->
                let hd, args = U.head_and_args_full t in
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
                    Range.dummyRange
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
                    let proj_1 = U.mk_field_projector_name (PC.mk_tuple_data_lid 2 rng) (S.null_bv S.tun) i in
                    let proj_1_tm = S.fv_to_tm (lid_as_fv proj_1 delta_equational None) in
                    S.mk_Tm_app (S.mk_Tm_uinst proj_1_tm [U_zero])
                                [S.iarg (type_of ea);
                                 S.iarg (type_of eb);
                                 S.as_arg ab]
                                rng
                in
                let shadow_a = map_shadow topt (proj 1) in
                let shadow_b = map_shadow topt (proj 2) in
                S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.lid_Mktuple2) [U_zero;U_zero])
                            [S.iarg (type_of ea);
                             S.iarg (type_of eb);
                             S.as_arg (embed ea (fst x) rng shadow_a norm);
                             S.as_arg (embed eb (snd x) rng shadow_b norm)]
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
                let hd, args = U.head_and_args_full t in
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

let e_either (ea:embedding<'a>) (eb:embedding<'b>) =
    let t_sum_a_b =
        let t_either = U.fvar_const PC.either_lid in
        S.mk_Tm_app t_either [S.as_arg ea.typ; S.as_arg eb.typ]
                    Range.dummyRange
    in
    let emb_t_sum_a_b =
        ET_app(PC.either_lid |> Ident.string_of_lid, [ea.emb_typ; eb.emb_typ])
    in
    let printer s =
        match s with
        | Inl a -> BU.format1 "Inl %s" (ea.print a)
        | Inr b -> BU.format1 "Inr %s" (eb.print b)
    in
    let em (s:either<'a,'b>) (rng:range) topt norm : term =
        lazy_embed
            printer
            emb_t_sum_a_b
            rng
            t_sum_a_b
            s
            (* Eagerly compute which closure we want, but thunk the actual embedding *)
            (match s with
             | Inl a ->
                (fun () ->
                let shadow_a = map_shadow topt (fun t ->
                  let v = Ident.mk_ident ("v", rng) in
                  let some_v = U.mk_field_projector_name_from_ident PC.inl_lid v in
                  let some_v_tm = S.fv_to_tm (lid_as_fv some_v delta_equational None) in
                  S.mk_Tm_app (S.mk_Tm_uinst some_v_tm [U_zero])
                              [S.iarg (type_of ea); S.iarg (type_of eb); S.as_arg t]
                              rng)
                in
                S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.inl_lid) [U_zero;U_zero])
                            [S.iarg (type_of ea);
                             S.iarg (type_of eb);
                             S.as_arg (embed ea a rng shadow_a norm)]
                            rng)
             | Inr b ->
                (fun () ->
                let shadow_b = map_shadow topt (fun t ->
                  let v = Ident.mk_ident ("v", rng) in
                  let some_v = U.mk_field_projector_name_from_ident PC.inr_lid v in
                  let some_v_tm = S.fv_to_tm (lid_as_fv some_v delta_equational None) in
                  S.mk_Tm_app (S.mk_Tm_uinst some_v_tm [U_zero])
                              [S.iarg (type_of ea); S.iarg (type_of eb); S.as_arg t]
                              rng)
                in
                S.mk_Tm_app (S.mk_Tm_uinst (S.tdataconstr PC.inr_lid) [U_zero;U_zero])
                            [S.iarg (type_of ea);
                             S.iarg (type_of eb);
                             S.as_arg (embed eb b rng shadow_b norm)]
                            rng)
             )
    in
    let un (t0:term) (w:bool) norm : option<either<'a, 'b>> =
        let t = U.unmeta_safe t0 in
        lazy_unembed
            printer
            emb_t_sum_a_b
            t
            t_sum_a_b
            (fun t ->
                let hd, args = U.head_and_args_full t in
                match (U.un_uinst hd).n, args with
                | Tm_fvar fv, [_; _; (a, _)] when S.fv_eq_lid fv PC.inl_lid ->
                    BU.bind_opt (unembed ea a w norm) (fun a ->
                    Some (Inl a))
                | Tm_fvar fv, [_; _; (b, _)] when S.fv_eq_lid fv PC.inr_lid ->
                    BU.bind_opt (unembed eb b w norm) (fun b ->
                    Some (Inr b))
                | _ ->
                    if w then
                    Err.log_issue t0.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded sum: %s" (Print.term_to_string t0)));
                    None)
    in
    mk_emb_full
        em
        un
        (S.t_either_of (type_of ea) (type_of eb))
        printer
        emb_t_sum_a_b

let e_list (ea:embedding<'a>) =
    let t_list_a =
        let t_list = U.fvar_const PC.list_lid in
        S.mk_Tm_app t_list [S.as_arg ea.typ] Range.dummyRange
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
                                rng
                  in
                  let shadow_hd = map_shadow shadow_l (proj "hd") in
                  let shadow_tl = map_shadow shadow_l (proj "tl") in
                  S.mk_Tm_app cons
                              [t;
                               S.as_arg (embed ea hd rng shadow_hd norm);
                               S.as_arg (em tl rng shadow_tl norm)]
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
                let hd, args = U.head_and_args_full t in
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
    | ZetaFull
    | Iota
    | Reify
    | UnfoldOnly  of list<string>
    | UnfoldFully of list<string>
    | UnfoldAttr  of list<string>
    | UnfoldQual  of list<string>
    | NBE
    | Unmeta

(* the steps as terms *)
let steps_Simpl         = tconst PC.steps_simpl
let steps_Weak          = tconst PC.steps_weak
let steps_HNF           = tconst PC.steps_hnf
let steps_Primops       = tconst PC.steps_primops
let steps_Delta         = tconst PC.steps_delta
let steps_Zeta          = tconst PC.steps_zeta
let steps_ZetaFull      = tconst PC.steps_zeta_full
let steps_Iota          = tconst PC.steps_iota
let steps_Reify         = tconst PC.steps_reify
let steps_UnfoldOnly    = tconst PC.steps_unfoldonly
let steps_UnfoldFully   = tconst PC.steps_unfoldonly
let steps_UnfoldAttr    = tconst PC.steps_unfoldattr
let steps_UnfoldQual    = tconst PC.steps_unfoldqual
let steps_NBE           = tconst PC.steps_nbe
let steps_Unmeta        = tconst PC.steps_unmeta

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
                | ZetaFull ->
                    steps_ZetaFull
                | Iota ->
                    steps_Iota
                | NBE ->
                    steps_NBE
                | Unmeta ->
                    steps_Unmeta
                | Reify ->
                    steps_Reify
                | UnfoldOnly l ->
                    S.mk_Tm_app steps_UnfoldOnly [S.as_arg (embed (e_list e_string) l rng None norm)]
                                rng
                | UnfoldFully l ->
                    S.mk_Tm_app steps_UnfoldFully [S.as_arg (embed (e_list e_string) l rng None norm)]
                                rng
                | UnfoldAttr l ->
                    S.mk_Tm_app steps_UnfoldAttr [S.as_arg (embed (e_list e_string) l rng None norm)]
                                rng
                | UnfoldQual l ->
                    S.mk_Tm_app steps_UnfoldQual [S.as_arg (embed (e_list e_string) l rng None norm)]
                                rng

                )
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
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_zeta_full ->
                    Some ZetaFull
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_iota ->
                    Some Iota
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_nbe ->
                    Some NBE
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_unmeta ->
                    Some Unmeta
                | Tm_fvar fv, [] when S.fv_eq_lid fv PC.steps_reify ->
                    Some Reify
                | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldonly ->
                    BU.bind_opt (unembed (e_list e_string) l w norm) (fun ss ->
                    Some <| UnfoldOnly ss)
                | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldfully ->
                    BU.bind_opt (unembed (e_list e_string) l w norm) (fun ss ->
                    Some <| UnfoldFully ss)
                | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldattr ->
                    BU.bind_opt (unembed (e_list e_string) l w norm) (fun ss ->
                    Some <| UnfoldAttr ss)
                | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv PC.steps_unfoldqual ->
                    BU.bind_opt (unembed (e_list e_string) l w norm) (fun ss ->
                    Some <| UnfoldQual ss)
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
        S.mk (Tm_constant (C.Const_range r)) rng
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

let e_vconfig =
    let em (vcfg:vconfig) (rng:Range.range) _shadow norm : term =
      (* The order is very important here, even if this is a record. *)
      S.mk_Tm_app (tdataconstr PC.mkvconfig_lid) // TODO: should this be a record constructor? does it matter?
                  [S.as_arg (embed e_fsint             vcfg.initial_fuel                              rng None norm);
                   S.as_arg (embed e_fsint             vcfg.max_fuel                                  rng None norm);
                   S.as_arg (embed e_fsint             vcfg.initial_ifuel                             rng None norm);
                   S.as_arg (embed e_fsint             vcfg.max_ifuel                                 rng None norm);
                   S.as_arg (embed e_bool              vcfg.detail_errors                             rng None norm);
                   S.as_arg (embed e_bool              vcfg.detail_hint_replay                        rng None norm);
                   S.as_arg (embed e_bool              vcfg.no_smt                                    rng None norm);
                   S.as_arg (embed e_fsint             vcfg.quake_lo                                  rng None norm);
                   S.as_arg (embed e_fsint             vcfg.quake_hi                                  rng None norm);
                   S.as_arg (embed e_bool              vcfg.quake_keep                                rng None norm);
                   S.as_arg (embed e_bool              vcfg.retry                                     rng None norm);
                   S.as_arg (embed e_bool              vcfg.smtencoding_elim_box                      rng None norm);
                   S.as_arg (embed e_string            vcfg.smtencoding_nl_arith_repr                 rng None norm);
                   S.as_arg (embed e_string            vcfg.smtencoding_l_arith_repr                  rng None norm);
                   S.as_arg (embed e_bool              vcfg.smtencoding_valid_intro                   rng None norm);
                   S.as_arg (embed e_bool              vcfg.smtencoding_valid_elim                    rng None norm);
                   S.as_arg (embed e_bool              vcfg.tcnorm                                    rng None norm);
                   S.as_arg (embed e_bool              vcfg.no_plugins                                rng None norm);
                   S.as_arg (embed e_bool              vcfg.no_tactics                                rng None norm);
                   S.as_arg (embed (e_option e_string) vcfg.vcgen_optimize_bind_as_seq                rng None norm);
                   S.as_arg (embed e_string_list       vcfg.z3cliopt                                  rng None norm);
                   S.as_arg (embed e_bool              vcfg.z3refresh                                 rng None norm);
                   S.as_arg (embed e_fsint             vcfg.z3rlimit                                  rng None norm);
                   S.as_arg (embed e_fsint             vcfg.z3rlimit_factor                           rng None norm);
                   S.as_arg (embed e_fsint             vcfg.z3seed                                    rng None norm);
                   S.as_arg (embed e_bool              vcfg.trivial_pre_for_unannotated_effectful_fns rng None norm);
                   S.as_arg (embed (e_option e_string) vcfg.reuse_hint_for                            rng None norm);
                  ]
                  rng
    in
    let un (t0:term) (w:bool) norm : option<vconfig> =
        let t = U.unascribe t0 in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        (* Sigh *)
        | Tm_fvar fv, [
            (initial_fuel, _);
            (max_fuel, _);
            (initial_ifuel, _);
            (max_ifuel, _);
            (detail_errors, _);
            (detail_hint_replay, _);
            (no_smt, _);
            (quake_lo, _);
            (quake_hi, _);
            (quake_keep, _);
            (retry, _);
            (smtencoding_elim_box, _);
            (smtencoding_nl_arith_repr, _);
            (smtencoding_l_arith_repr, _);
            (smtencoding_valid_intro, _);
            (smtencoding_valid_elim, _);
            (tcnorm, _);
            (no_plugins, _);
            (no_tactics, _);
            (vcgen_optimize_bind_as_seq, _);
            (z3cliopt, _);
            (z3refresh, _);
            (z3rlimit, _);
            (z3rlimit_factor, _);
            (z3seed, _);
            (trivial_pre_for_unannotated_effectful_fns, _);
            (reuse_hint_for, _)
            ] when S.fv_eq_lid fv PC.mkvconfig_lid ->
                  BU.bind_opt (unembed e_fsint             initial_fuel w norm) (fun initial_fuel ->
                  BU.bind_opt (unembed e_fsint             max_fuel w norm) (fun max_fuel ->
                  BU.bind_opt (unembed e_fsint             initial_ifuel w norm) (fun initial_ifuel ->
                  BU.bind_opt (unembed e_fsint             max_ifuel w norm) (fun max_ifuel ->
                  BU.bind_opt (unembed e_bool              detail_errors w norm) (fun detail_errors ->
                  BU.bind_opt (unembed e_bool              detail_hint_replay w norm) (fun detail_hint_replay ->
                  BU.bind_opt (unembed e_bool              no_smt w norm) (fun no_smt ->
                  BU.bind_opt (unembed e_fsint             quake_lo w norm) (fun quake_lo ->
                  BU.bind_opt (unembed e_fsint             quake_hi w norm) (fun quake_hi ->
                  BU.bind_opt (unembed e_bool              quake_keep w norm) (fun quake_keep ->
                  BU.bind_opt (unembed e_bool              retry w norm) (fun retry ->
                  BU.bind_opt (unembed e_bool              smtencoding_elim_box w norm) (fun smtencoding_elim_box ->
                  BU.bind_opt (unembed e_string            smtencoding_nl_arith_repr w norm) (fun smtencoding_nl_arith_repr ->
                  BU.bind_opt (unembed e_string            smtencoding_l_arith_repr w norm) (fun smtencoding_l_arith_repr ->
                  BU.bind_opt (unembed e_bool              smtencoding_valid_intro w norm) (fun smtencoding_valid_intro ->
                  BU.bind_opt (unembed e_bool              smtencoding_valid_elim w norm) (fun smtencoding_valid_elim ->
                  BU.bind_opt (unembed e_bool              tcnorm w norm) (fun tcnorm ->
                  BU.bind_opt (unembed e_bool              no_plugins w norm) (fun no_plugins ->
                  BU.bind_opt (unembed e_bool              no_tactics w norm) (fun no_tactics ->
                  BU.bind_opt (unembed (e_option e_string) vcgen_optimize_bind_as_seq w norm) (fun vcgen_optimize_bind_as_seq ->
                  BU.bind_opt (unembed e_string_list       z3cliopt w norm) (fun z3cliopt ->
                  BU.bind_opt (unembed e_bool              z3refresh w norm) (fun z3refresh ->
                  BU.bind_opt (unembed e_fsint             z3rlimit w norm) (fun z3rlimit ->
                  BU.bind_opt (unembed e_fsint             z3rlimit_factor w norm) (fun z3rlimit_factor ->
                  BU.bind_opt (unembed e_fsint             z3seed w norm) (fun z3seed ->
                  BU.bind_opt (unembed e_bool              trivial_pre_for_unannotated_effectful_fns w norm) (fun trivial_pre_for_unannotated_effectful_fns ->
                  BU.bind_opt (unembed (e_option e_string) reuse_hint_for w norm) (fun reuse_hint_for ->
                  Some ({
                    initial_fuel = initial_fuel;
                    max_fuel = max_fuel;
                    initial_ifuel = initial_ifuel;
                    max_ifuel = max_ifuel;
                    detail_errors = detail_errors;
                    detail_hint_replay = detail_hint_replay;
                    no_smt = no_smt;
                    quake_lo = quake_lo;
                    quake_hi = quake_hi;
                    quake_keep = quake_keep;
                    retry = retry;
                    smtencoding_elim_box = smtencoding_elim_box;
                    smtencoding_nl_arith_repr = smtencoding_nl_arith_repr;
                    smtencoding_l_arith_repr = smtencoding_l_arith_repr;
                    smtencoding_valid_intro = smtencoding_valid_intro;
                    smtencoding_valid_elim = smtencoding_valid_elim;
                    tcnorm = tcnorm;
                    no_plugins = no_plugins;
                    no_tactics = no_tactics;
                    vcgen_optimize_bind_as_seq = vcgen_optimize_bind_as_seq;
                    z3cliopt = z3cliopt;
                    z3refresh = z3refresh;
                    z3rlimit = z3rlimit;
                    z3rlimit_factor = z3rlimit_factor;
                    z3seed = z3seed;
                    trivial_pre_for_unannotated_effectful_fns = trivial_pre_for_unannotated_effectful_fns;
                    reuse_hint_for = reuse_hint_for;
                  }))))))))))))))))))))))))))))
        | _ ->
          if w then
            Err.log_issue t0.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded vconfig: %s" (Print.term_to_string t0)));
          None
    in
    mk_emb_full
        em
        un
        S.t_vconfig
        (fun _ -> "vconfig")
        (ET_app (PC.vconfig_lid |> Ident.string_of_lid, []))

let or_else (f: option<'a>) (g:unit -> 'a) =
    match f with
    | Some x -> x
    | None -> g ()

let e_arrow (ea:embedding<'a>) (eb:embedding<'b>) : embedding<('a -> 'b)> =
    let t_arrow =
        S.mk (Tm_arrow([S.mk_binder (S.null_bv ea.typ)],
                        S.mk_Total eb.typ))
              Range.dummyRange
    in
    let emb_t_arr_a_b = ET_fun(ea.emb_typ, eb.emb_typ) in
    let printer (f:'a -> 'b) = "<fun>" in
    let em (f:'a -> 'b) rng shadow_f norm =
        // let f_wrapped (x:term) =
        //     let shadow_app = map_shadow shadow_f (fun f ->
        //         S.mk_Tm_app f [S.as_arg x] None rng)
        //     in
        //     or_else
        //     (BU.map_opt (unembed ea x true norm) (fun x ->
        //         embed eb (f x) rng shadow_app norm))
        //     (fun () ->
        //         match force_shadow shadow_app with
        //         | None -> raise Embedding_failure
        //         | Some app -> norm (BU.Inr app))
        // in
        lazy_embed
            (fun _ -> "<fun>")
            emb_t_arr_a_b
            rng
            t_arrow
            f //f_wrapped
            (fun () ->
                match force_shadow shadow_f with
                | None -> raise Embedding_failure //TODO: dodgy
                | Some repr_f ->
                  if !Options.debug_embedding then
                  BU.print2 "e_arrow forced back to term using shadow %s; repr=%s\n"
                                   (Print.term_to_string repr_f)
                                   (BU.stack_dump());
                  let res = norm (Inr repr_f) in
                  if !Options.debug_embedding then
                  BU.print3 "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                                   (Print.term_to_string repr_f)
                                   (Print.term_to_string res)
                                   (BU.stack_dump());
                  res)
    in
    let un (f:term) w norm : option<('a -> 'b)> =
        lazy_unembed
            printer
            emb_t_arr_a_b
            f
            t_arrow
            (fun f ->
                let f_wrapped (a:'a) : 'b =
                    if !Options.debug_embedding then
                    BU.print2 "Calling back into normalizer for %s\n%s\n"
                              (Print.term_to_string f)
                              (BU.stack_dump());
                    let a_tm = embed ea a f.pos None norm in
                    let b_tm = norm (Inr (S.mk_Tm_app f [S.as_arg a_tm] f.pos)) in
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
            Some (Thunk.mk (fun () -> S.mk_Tm_app (norm (Inl fv_lid)) args rng))
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
            Some (Thunk.mk (fun () -> S.mk_Tm_app (norm (Inl fv_lid)) args rng))
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
            Some (Thunk.mk (fun () -> S.mk_Tm_app (norm (Inl fv_lid)) args rng))
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

let debug_wrap (s:string) (f:unit -> 'a) =
    if !Options.debug_embedding
    then BU.print1 "++++starting %s\n" s;
    let res = f () in
    if !Options.debug_embedding
    then BU.print1 "------ending %s\n" s;
    res
