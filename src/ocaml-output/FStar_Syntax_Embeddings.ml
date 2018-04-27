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
          let uu____827 =
            let uu____840 =
              let uu____841 = FStar_Syntax_Util.un_uinst hd1  in
              uu____841.FStar_Syntax_Syntax.n  in
            (uu____840, args)  in
          (match uu____827 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____857) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____877::(a,uu____879)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____916 = unembed ea a  in
               FStar_Util.bind_opt uu____916
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____925 ->
               (if w
                then
                  (let uu____939 =
                     let uu____944 =
                       let uu____945 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____945
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____944)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____939)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____949 =
      let uu____950 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____950  in
    mk_emb em un uu____949
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____1006 =
          let uu____1011 =
            let uu____1012 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1012
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____1013 =
            let uu____1014 =
              let uu____1021 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1021  in
            let uu____1022 =
              let uu____1031 =
                let uu____1038 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____1038  in
              let uu____1039 =
                let uu____1048 =
                  let uu____1055 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____1055  in
                let uu____1056 =
                  let uu____1065 =
                    let uu____1072 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____1072  in
                  [uu____1065]  in
                uu____1048 :: uu____1056  in
              uu____1031 :: uu____1039  in
            uu____1014 :: uu____1022  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1011 uu____1013  in
        uu____1006 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1129 = FStar_Syntax_Util.head_and_args t  in
        match uu____1129 with
        | (hd1,args) ->
            let uu____1166 =
              let uu____1177 =
                let uu____1178 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1178.FStar_Syntax_Syntax.n  in
              (uu____1177, args)  in
            (match uu____1166 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1194::uu____1195::(a,uu____1197)::(b,uu____1199)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1234 = unembed ea a  in
                 FStar_Util.bind_opt uu____1234
                   (fun a1  ->
                      let uu____1244 = unembed eb b  in
                      FStar_Util.bind_opt uu____1244
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1257 ->
                 (if w
                  then
                    (let uu____1269 =
                       let uu____1274 =
                         let uu____1275 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1275
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1274)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1269)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1281 =
        let uu____1282 = type_of ea  in
        let uu____1283 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1282 uu____1283  in
      mk_emb em un uu____1281
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1322 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1322
         in
      let nil =
        let uu____1326 =
          let uu____1331 =
            let uu____1332 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1332
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1331 [t]  in
        uu____1326 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1348 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1348
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1356 =
               let uu____1361 =
                 let uu____1362 =
                   let uu____1371 =
                     let uu____1378 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1378  in
                   let uu____1379 =
                     let uu____1388 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1388]  in
                   uu____1371 :: uu____1379  in
                 t :: uu____1362  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1361  in
             uu____1356 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1441 = FStar_Syntax_Util.head_and_args t  in
      match uu____1441 with
      | (hd1,args) ->
          let uu____1476 =
            let uu____1487 =
              let uu____1488 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1488.FStar_Syntax_Syntax.n  in
            (uu____1487, args)  in
          (match uu____1476 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1502) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,_t::(hd2,uu____1520)::(tl1,uu____1522)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1549 = unembed ea hd2  in
               FStar_Util.bind_opt uu____1549
                 (fun hd3  ->
                    let uu____1557 = un w tl1  in
                    FStar_Util.bind_opt uu____1557
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1572 ->
               (if w
                then
                  (let uu____1584 =
                     let uu____1589 =
                       let uu____1590 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1590
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1589)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1584)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1594 =
      let uu____1595 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1595  in
    mk_emb em un uu____1594
  
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
    match projectee with | Simpl  -> true | uu____1626 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1632 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1638 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1644 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1650 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1656 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1662 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1671 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1693 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1713 -> false
  
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
        let uu____1737 =
          let uu____1742 =
            let uu____1743 =
              let uu____1750 =
                let uu____1751 = e_list e_string  in embed uu____1751 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1750  in
            [uu____1743]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1742  in
        uu____1737 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____1775 =
          let uu____1780 =
            let uu____1781 =
              let uu____1788 =
                let uu____1789 = e_list e_string  in embed uu____1789 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1788  in
            [uu____1781]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____1780  in
        uu____1775 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____1811 =
          let uu____1816 =
            let uu____1817 = FStar_Syntax_Syntax.as_arg a  in [uu____1817]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1816  in
        uu____1811 FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____1854 = FStar_Syntax_Util.head_and_args t  in
    match uu____1854 with
    | (hd1,args) ->
        let uu____1887 =
          let uu____1900 =
            let uu____1901 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1901.FStar_Syntax_Syntax.n  in
          (uu____1900, args)  in
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2021)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____2046 =
               let uu____2051 = e_list e_string  in unembed uu____2051 l  in
             FStar_Util.bind_opt uu____2046
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2068)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____2093 =
               let uu____2098 = e_list e_string  in unembed uu____2098 l  in
             FStar_Util.bind_opt uu____2093
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2114::(a,uu____2116)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____2153 ->
             (if w
              then
                (let uu____2167 =
                   let uu____2172 =
                     let uu____2173 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____2173
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2172)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2167)
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
    | uu____2207 ->
        (if w
         then
           (let uu____2209 =
              let uu____2214 =
                let uu____2215 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____2215  in
              (FStar_Errors.Warning_NotEmbedded, uu____2214)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2209)
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
          | (x,uu____2285)::[] ->
              let uu____2302 = ua x  in
              FStar_Util.bind_opt uu____2302
                (fun a  ->
                   let uu____2308 =
                     let uu____2309 =
                       let uu____2310 =
                         let uu____2311 = ua x  in FStar_Util.must uu____2311
                          in
                       f uu____2310  in
                     eb1 FStar_Range.dummyRange uu____2309  in
                   FStar_Pervasives_Native.Some uu____2308)
          | uu____2314 -> FStar_Pervasives_Native.None
  
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
            | (x,uu____2409)::(y,uu____2411)::[] ->
                let uu____2438 = ua x  in
                FStar_Util.bind_opt uu____2438
                  (fun a  ->
                     let uu____2444 = ub y  in
                     FStar_Util.bind_opt uu____2444
                       (fun b  ->
                          let uu____2450 =
                            let uu____2451 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2451  in
                          FStar_Pervasives_Native.Some uu____2450))
            | uu____2452 -> FStar_Pervasives_Native.None
  
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
              | (x,uu____2573)::(y,uu____2575)::(z,uu____2577)::[] ->
                  let uu____2614 = ua x  in
                  FStar_Util.bind_opt uu____2614
                    (fun a  ->
                       let uu____2620 = ub y  in
                       FStar_Util.bind_opt uu____2620
                         (fun b  ->
                            let uu____2626 = uc z  in
                            FStar_Util.bind_opt uu____2626
                              (fun c  ->
                                 let uu____2632 =
                                   let uu____2633 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____2633  in
                                 FStar_Pervasives_Native.Some uu____2632)))
              | uu____2634 -> FStar_Pervasives_Native.None
  