open Prims
type 'a embedding =
  {
  em: FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term ;
  un:
    Prims.bool ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
    ;
  typ: FStar_Syntax_Syntax.typ }[@@deriving show]
let __proj__Mkembedding__item__em :
  'a . 'a embedding -> FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__em
  
let __proj__Mkembedding__item__un :
  'a .
    'a embedding ->
      Prims.bool ->
        FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__un
  
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__typ
  
let embed :
  'a . 'a embedding -> FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term =
  fun e  -> fun r  -> fun x  -> e.em r x 
let unembed' :
  'a .
    'a embedding ->
      Prims.bool ->
        FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  = fun e  -> fun b  -> fun t  -> e.un b t 
let unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  = fun e  -> fun t  -> e.un true t 
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  = fun e  -> fun t  -> e.un false t 
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
type 'a raw_embedder = FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
[@@deriving show]
type 'a raw_unembedder' =
  Prims.bool -> FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
[@@deriving show]
type 'a raw_unembedder =
  FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option[@@deriving
                                                                 show]
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder' -> FStar_Syntax_Syntax.typ -> 'a embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em r t = t  in
  let un b t = FStar_Pervasives_Native.Some t  in
  let typ = FStar_Syntax_Syntax.t_term  in mk_emb em un typ 
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  -> { em = (e_any.em); un = (e_any.un); typ } 
let (e_unit : unit embedding) =
  let em rng u =
    let uu___50_418 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___50_418.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___50_418.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____439 ->
        (if w
         then
           (let uu____441 =
              let uu____446 =
                let uu____447 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____447  in
              (FStar_Errors.Warning_NotEmbedded, uu____446)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____441)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_unit 
let (e_bool : Prims.bool embedding) =
  let em rng b =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___51_468 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___51_468.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___51_468.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____490 ->
        (if w
         then
           (let uu____492 =
              let uu____497 =
                let uu____498 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____498  in
              (FStar_Errors.Warning_NotEmbedded, uu____497)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____492)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_bool 
let (e_char : FStar_Char.char embedding) =
  let em rng c =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___52_517 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___52_517.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___52_517.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____541 ->
        (if w
         then
           (let uu____543 =
              let uu____548 =
                let uu____549 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____549  in
              (FStar_Errors.Warning_NotEmbedded, uu____548)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____543)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let em rng i =
    let t =
      let uu____567 = FStar_BigInt.string_of_big_int i  in
      FStar_Syntax_Util.exp_int uu____567  in
    let uu___53_568 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___53_568.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___53_568.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____588))
        ->
        let uu____601 = FStar_BigInt.big_int_of_string s  in
        FStar_Pervasives_Native.Some uu____601
    | uu____602 ->
        (if w
         then
           (let uu____604 =
              let uu____609 =
                let uu____610 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded int: %s" uu____610  in
              (FStar_Errors.Warning_NotEmbedded, uu____609)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____604)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_int 
let (e_string : Prims.string embedding) =
  let em rng s =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____644)) -> FStar_Pervasives_Native.Some s
    | uu____645 ->
        (if w
         then
           (let uu____647 =
              let uu____652 =
                let uu____653 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____653  in
              (FStar_Errors.Warning_NotEmbedded, uu____652)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____647)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_string 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em rng o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____688 =
            let uu____693 =
              let uu____694 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____694
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____695 =
              let uu____696 =
                let uu____703 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____703  in
              [uu____696]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____693 uu____695  in
          uu____688 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____719 =
            let uu____724 =
              let uu____725 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____725
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____726 =
              let uu____727 =
                let uu____734 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____734  in
              let uu____735 =
                let uu____744 =
                  let uu____751 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____751  in
                [uu____744]  in
              uu____727 :: uu____735  in
            FStar_Syntax_Syntax.mk_Tm_app uu____724 uu____726  in
          uu____719 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____792 = FStar_Syntax_Util.head_and_args t  in
      match uu____792 with
      | (hd1,args) ->
          let uu____833 =
            let uu____844 =
              let uu____845 = FStar_Syntax_Util.un_uinst hd1  in
              uu____845.FStar_Syntax_Syntax.n  in
            (uu____844, args)  in
          (match uu____833 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____859) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____875::(a,uu____877)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____900 = unembed ea a  in
               FStar_Util.bind_opt uu____900
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____909 ->
               (if w
                then
                  (let uu____921 =
                     let uu____926 =
                       let uu____927 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____927
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____926)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____921)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____931 =
      let uu____932 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____932  in
    mk_emb em un uu____931
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____988 =
          let uu____993 =
            let uu____994 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____994
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____995 =
            let uu____996 =
              let uu____1003 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1003  in
            let uu____1004 =
              let uu____1013 =
                let uu____1020 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____1020  in
              let uu____1021 =
                let uu____1030 =
                  let uu____1037 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____1037  in
                let uu____1038 =
                  let uu____1047 =
                    let uu____1054 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____1054  in
                  [uu____1047]  in
                uu____1030 :: uu____1038  in
              uu____1013 :: uu____1021  in
            uu____996 :: uu____1004  in
          FStar_Syntax_Syntax.mk_Tm_app uu____993 uu____995  in
        uu____988 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1111 = FStar_Syntax_Util.head_and_args t  in
        match uu____1111 with
        | (hd1,args) ->
            let uu____1154 =
              let uu____1165 =
                let uu____1166 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1166.FStar_Syntax_Syntax.n  in
              (uu____1165, args)  in
            (match uu____1154 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1182::uu____1183::(a,uu____1185)::(b,uu____1187)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1222 = unembed ea a  in
                 FStar_Util.bind_opt uu____1222
                   (fun a1  ->
                      let uu____1232 = unembed eb b  in
                      FStar_Util.bind_opt uu____1232
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1245 ->
                 (if w
                  then
                    (let uu____1257 =
                       let uu____1262 =
                         let uu____1263 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1263
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1262)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1257)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1269 =
        let uu____1270 = type_of ea  in
        let uu____1271 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1270 uu____1271  in
      mk_emb em un uu____1269
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1310 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1310
         in
      let nil =
        let uu____1314 =
          let uu____1319 =
            let uu____1320 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1320
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1319 [t]  in
        uu____1314 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1336 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1336
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1344 =
               let uu____1349 =
                 let uu____1350 =
                   let uu____1359 =
                     let uu____1366 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1366  in
                   let uu____1367 =
                     let uu____1376 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1376]  in
                   uu____1359 :: uu____1367  in
                 t :: uu____1350  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1349  in
             uu____1344 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1429 = FStar_Syntax_Util.head_and_args t  in
      match uu____1429 with
      | (hd1,args) ->
          let uu____1470 =
            let uu____1481 =
              let uu____1482 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1482.FStar_Syntax_Syntax.n  in
            (uu____1481, args)  in
          (match uu____1470 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1496) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,_t::(hd2,uu____1514)::(tl1,uu____1516)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1543 = unembed ea hd2  in
               FStar_Util.bind_opt uu____1543
                 (fun hd3  ->
                    let uu____1551 = un w tl1  in
                    FStar_Util.bind_opt uu____1551
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1566 ->
               (if w
                then
                  (let uu____1578 =
                     let uu____1583 =
                       let uu____1584 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1584
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1583)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1578)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1588 =
      let uu____1589 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1589  in
    mk_emb em un uu____1588
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | Iota 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute [@@deriving show]
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____1620 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1626 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1632 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1638 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1644 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1650 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1656 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1665 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1687 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1707 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (steps_Simpl : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_simpl 
let (steps_Weak : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_weak 
let (steps_HNF : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_hnf 
let (steps_Primops : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_primops 
let (steps_Delta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_delta 
let (steps_Zeta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_zeta 
let (steps_Iota : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_iota 
let (steps_UnfoldOnly : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldFully : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldattr 
let (e_norm_step : norm_step embedding) =
  let em rng n1 =
    match n1 with
    | Simpl  -> steps_Simpl
    | Weak  -> steps_Weak
    | HNF  -> steps_HNF
    | Primops  -> steps_Primops
    | Delta  -> steps_Delta
    | Zeta  -> steps_Zeta
    | Iota  -> steps_Iota
    | UnfoldOnly l ->
        let uu____1731 =
          let uu____1736 =
            let uu____1737 =
              let uu____1744 =
                let uu____1745 = e_list e_string  in embed uu____1745 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1744  in
            [uu____1737]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1736  in
        uu____1731 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____1769 =
          let uu____1774 =
            let uu____1775 =
              let uu____1782 =
                let uu____1783 = e_list e_string  in embed uu____1783 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1782  in
            [uu____1775]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____1774  in
        uu____1769 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____1805 =
          let uu____1810 =
            let uu____1811 = FStar_Syntax_Syntax.as_arg a  in [uu____1811]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1810  in
        uu____1805 FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____1848 = FStar_Syntax_Util.head_and_args t  in
    match uu____1848 with
    | (hd1,args) ->
        let uu____1887 =
          let uu____1898 =
            let uu____1899 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1899.FStar_Syntax_Syntax.n  in
          (uu____1898, args)  in
        (match uu____1887 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl
             -> FStar_Pervasives_Native.Some Simpl
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak
             -> FStar_Pervasives_Native.Some Weak
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
             FStar_Pervasives_Native.Some HNF
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_primops
             -> FStar_Pervasives_Native.Some Primops
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta
             -> FStar_Pervasives_Native.Some Delta
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta
             -> FStar_Pervasives_Native.Some Zeta
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota
             -> FStar_Pervasives_Native.Some Iota
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1989)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____2004 =
               let uu____2009 = e_list e_string  in unembed uu____2009 l  in
             FStar_Util.bind_opt uu____2004
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2026)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____2041 =
               let uu____2046 = e_list e_string  in unembed uu____2046 l  in
             FStar_Util.bind_opt uu____2041
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2062::(a,uu____2064)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____2087 ->
             (if w
              then
                (let uu____2099 =
                   let uu____2104 =
                     let uu____2105 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____2105
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2104)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2099)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb em un FStar_Syntax_Syntax.t_norm_step 
let (e_range : FStar_Range.range embedding) =
  let em rng r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu____2139 ->
        (if w
         then
           (let uu____2141 =
              let uu____2146 =
                let uu____2147 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____2147  in
              (FStar_Errors.Warning_NotEmbedded, uu____2146)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2141)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_range 
let embed_arrow_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun f  ->
        fun args  ->
          let ua = unembed ea  in
          let eb1 = embed eb  in
          match args with
          | (x,uu____2217)::[] ->
              let uu____2234 = ua x  in
              FStar_Util.bind_opt uu____2234
                (fun a  ->
                   let uu____2240 =
                     let uu____2241 =
                       let uu____2242 =
                         let uu____2243 = ua x  in FStar_Util.must uu____2243
                          in
                       f uu____2242  in
                     eb1 FStar_Range.dummyRange uu____2241  in
                   FStar_Pervasives_Native.Some uu____2240)
          | uu____2246 -> FStar_Pervasives_Native.None
  
let embed_arrow_2 :
  'a 'b 'c .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          ('a -> 'b -> 'c) ->
            FStar_Syntax_Syntax.args ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun f  ->
          fun args  ->
            let ua = unembed ea  in
            let ub = unembed eb  in
            let ec1 = embed ec  in
            match args with
            | (x,uu____2341)::(y,uu____2343)::[] ->
                let uu____2370 = ua x  in
                FStar_Util.bind_opt uu____2370
                  (fun a  ->
                     let uu____2376 = ub y  in
                     FStar_Util.bind_opt uu____2376
                       (fun b  ->
                          let uu____2382 =
                            let uu____2383 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2383  in
                          FStar_Pervasives_Native.Some uu____2382))
            | uu____2384 -> FStar_Pervasives_Native.None
  
let embed_arrow_3 :
  'a 'b 'c 'd .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          'd embedding ->
            ('a -> 'b -> 'c -> 'd) ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun f  ->
            fun args  ->
              let ua = unembed ea  in
              let ub = unembed eb  in
              let uc = unembed ec  in
              let ed1 = embed ed  in
              match args with
              | (x,uu____2505)::(y,uu____2507)::(z,uu____2509)::[] ->
                  let uu____2546 = ua x  in
                  FStar_Util.bind_opt uu____2546
                    (fun a  ->
                       let uu____2552 = ub y  in
                       FStar_Util.bind_opt uu____2552
                         (fun b  ->
                            let uu____2558 = uc z  in
                            FStar_Util.bind_opt uu____2558
                              (fun c  ->
                                 let uu____2564 =
                                   let uu____2565 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____2565  in
                                 FStar_Pervasives_Native.Some uu____2564)))
              | uu____2566 -> FStar_Pervasives_Native.None
  