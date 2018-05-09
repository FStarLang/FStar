open Prims
type 'a embedding =
  {
  em: FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term ;
  un:
    Prims.bool ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
    ;
  typ: FStar_Syntax_Syntax.typ }
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
    Prims.bool ->
      'a embedding ->
        FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  = fun b  -> fun e  -> fun t  -> e.un b t 
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
type 'a raw_unembedder' =
  Prims.bool -> FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
type 'a raw_unembedder =
  FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
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
    let uu___77_418 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___77_418.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___77_418.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____437 ->
        (if w
         then
           (let uu____439 =
              let uu____444 =
                let uu____445 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____445  in
              (FStar_Errors.Warning_NotEmbedded, uu____444)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____439)
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
    let uu___78_466 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___78_466.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___78_466.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____488 ->
        (if w
         then
           (let uu____490 =
              let uu____495 =
                let uu____496 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____496  in
              (FStar_Errors.Warning_NotEmbedded, uu____495)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____490)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_bool 
let (e_char : FStar_Char.char embedding) =
  let em rng c =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___79_515 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___79_515.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___79_515.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____539 ->
        (if w
         then
           (let uu____541 =
              let uu____546 =
                let uu____547 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____547  in
              (FStar_Errors.Warning_NotEmbedded, uu____546)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____541)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let em rng i =
    let t =
      let uu____565 = FStar_BigInt.string_of_big_int i  in
      FStar_Syntax_Util.exp_int uu____565  in
    let uu___80_566 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___80_566.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___80_566.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____586))
        ->
        let uu____599 = FStar_BigInt.big_int_of_string s  in
        FStar_Pervasives_Native.Some uu____599
    | uu____600 ->
        (if w
         then
           (let uu____602 =
              let uu____607 =
                let uu____608 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded int: %s" uu____608  in
              (FStar_Errors.Warning_NotEmbedded, uu____607)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____602)
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
        (s,uu____642)) -> FStar_Pervasives_Native.Some s
    | uu____643 ->
        (if w
         then
           (let uu____645 =
              let uu____650 =
                let uu____651 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____651  in
              (FStar_Errors.Warning_NotEmbedded, uu____650)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____645)
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
          let uu____686 =
            let uu____691 =
              let uu____692 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____692
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____693 =
              let uu____694 =
                let uu____701 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____701  in
              [uu____694]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____691 uu____693  in
          uu____686 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____717 =
            let uu____722 =
              let uu____723 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____723
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____724 =
              let uu____725 =
                let uu____732 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____732  in
              let uu____733 =
                let uu____742 =
                  let uu____749 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____749  in
                [uu____742]  in
              uu____725 :: uu____733  in
            FStar_Syntax_Syntax.mk_Tm_app uu____722 uu____724  in
          uu____717 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____790 = FStar_Syntax_Util.head_and_args t  in
      match uu____790 with
      | (hd1,args) ->
          let uu____831 =
            let uu____844 =
              let uu____845 = FStar_Syntax_Util.un_uinst hd1  in
              uu____845.FStar_Syntax_Syntax.n  in
            (uu____844, args)  in
          (match uu____831 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____861) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____881::(a,uu____883)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____920 = unembed' w ea a  in
               FStar_Util.bind_opt uu____920
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____929 ->
               (if w
                then
                  (let uu____943 =
                     let uu____948 =
                       let uu____949 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____949
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____948)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____943)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____953 =
      let uu____954 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____954  in
    mk_emb em un uu____953
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____1010 =
          let uu____1015 =
            let uu____1016 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1016
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____1017 =
            let uu____1018 =
              let uu____1025 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1025  in
            let uu____1026 =
              let uu____1035 =
                let uu____1042 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____1042  in
              let uu____1043 =
                let uu____1052 =
                  let uu____1059 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____1059  in
                let uu____1060 =
                  let uu____1069 =
                    let uu____1076 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____1076  in
                  [uu____1069]  in
                uu____1052 :: uu____1060  in
              uu____1035 :: uu____1043  in
            uu____1018 :: uu____1026  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1015 uu____1017  in
        uu____1010 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1133 = FStar_Syntax_Util.head_and_args t  in
        match uu____1133 with
        | (hd1,args) ->
            let uu____1176 =
              let uu____1187 =
                let uu____1188 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1188.FStar_Syntax_Syntax.n  in
              (uu____1187, args)  in
            (match uu____1176 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1204::uu____1205::(a,uu____1207)::(b,uu____1209)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1244 = unembed' w ea a  in
                 FStar_Util.bind_opt uu____1244
                   (fun a1  ->
                      let uu____1254 = unembed' w eb b  in
                      FStar_Util.bind_opt uu____1254
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1267 ->
                 (if w
                  then
                    (let uu____1279 =
                       let uu____1284 =
                         let uu____1285 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1285
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1284)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1279)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1291 =
        let uu____1292 = type_of ea  in
        let uu____1293 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1292 uu____1293  in
      mk_emb em un uu____1291
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1332 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1332
         in
      let nil =
        let uu____1336 =
          let uu____1341 =
            let uu____1342 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1342
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1341 [t]  in
        uu____1336 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1358 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1358
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1366 =
               let uu____1371 =
                 let uu____1372 =
                   let uu____1381 =
                     let uu____1388 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1388  in
                   let uu____1389 =
                     let uu____1398 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1398]  in
                   uu____1381 :: uu____1389  in
                 t :: uu____1372  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1371  in
             uu____1366 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1451 = FStar_Syntax_Util.head_and_args t  in
      match uu____1451 with
      | (hd1,args) ->
          let uu____1492 =
            let uu____1505 =
              let uu____1506 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1506.FStar_Syntax_Syntax.n  in
            (uu____1505, args)  in
          (match uu____1492 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1522) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(uu____1542,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit uu____1543))::(hd2,FStar_Pervasives_Native.None
                                                               )::(tl1,FStar_Pervasives_Native.None
                                                                   )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1584 = unembed' w ea hd2  in
               FStar_Util.bind_opt uu____1584
                 (fun hd3  ->
                    let uu____1592 = un w tl1  in
                    FStar_Util.bind_opt uu____1592
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                       )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1640 = unembed' w ea hd2  in
               FStar_Util.bind_opt uu____1640
                 (fun hd3  ->
                    let uu____1648 = un w tl1  in
                    FStar_Util.bind_opt uu____1648
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1663 ->
               (if w
                then
                  (let uu____1677 =
                     let uu____1682 =
                       let uu____1683 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1683
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1682)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1677)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1687 =
      let uu____1688 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1688  in
    mk_emb em un uu____1687
  
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
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____1719 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1725 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1731 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1737 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1743 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1749 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1755 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1764 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1786 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1806 -> false
  
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
        let uu____1830 =
          let uu____1835 =
            let uu____1836 =
              let uu____1843 =
                let uu____1844 = e_list e_string  in embed uu____1844 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1843  in
            [uu____1836]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1835  in
        uu____1830 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____1868 =
          let uu____1873 =
            let uu____1874 =
              let uu____1881 =
                let uu____1882 = e_list e_string  in embed uu____1882 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1881  in
            [uu____1874]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____1873  in
        uu____1868 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____1904 =
          let uu____1909 =
            let uu____1910 = FStar_Syntax_Syntax.as_arg a  in [uu____1910]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1909  in
        uu____1904 FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____1947 = FStar_Syntax_Util.head_and_args t  in
    match uu____1947 with
    | (hd1,args) ->
        let uu____1986 =
          let uu____1999 =
            let uu____2000 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2000.FStar_Syntax_Syntax.n  in
          (uu____1999, args)  in
        (match uu____1986 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2120)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____2145 =
               let uu____2150 = e_list e_string  in unembed' w uu____2150 l
                in
             FStar_Util.bind_opt uu____2145
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2167)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____2192 =
               let uu____2197 = e_list e_string  in unembed' w uu____2197 l
                in
             FStar_Util.bind_opt uu____2192
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2213::(a,uu____2215)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____2252 ->
             (if w
              then
                (let uu____2266 =
                   let uu____2271 =
                     let uu____2272 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____2272
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2271)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2266)
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
    | uu____2306 ->
        (if w
         then
           (let uu____2308 =
              let uu____2313 =
                let uu____2314 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____2314  in
              (FStar_Errors.Warning_NotEmbedded, uu____2313)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2308)
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
          | (x,uu____2384)::[] ->
              let uu____2401 = ua x  in
              FStar_Util.bind_opt uu____2401
                (fun a  ->
                   let uu____2407 =
                     let uu____2408 =
                       let uu____2409 =
                         let uu____2410 = ua x  in FStar_Util.must uu____2410
                          in
                       f uu____2409  in
                     eb1 FStar_Range.dummyRange uu____2408  in
                   FStar_Pervasives_Native.Some uu____2407)
          | uu____2413 -> FStar_Pervasives_Native.None
  
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
            | (x,uu____2508)::(y,uu____2510)::[] ->
                let uu____2537 = ua x  in
                FStar_Util.bind_opt uu____2537
                  (fun a  ->
                     let uu____2543 = ub y  in
                     FStar_Util.bind_opt uu____2543
                       (fun b  ->
                          let uu____2549 =
                            let uu____2550 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2550  in
                          FStar_Pervasives_Native.Some uu____2549))
            | uu____2551 -> FStar_Pervasives_Native.None
  
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
              | (x,uu____2672)::(y,uu____2674)::(z,uu____2676)::[] ->
                  let uu____2713 = ua x  in
                  FStar_Util.bind_opt uu____2713
                    (fun a  ->
                       let uu____2719 = ub y  in
                       FStar_Util.bind_opt uu____2719
                         (fun b  ->
                            let uu____2725 = uc z  in
                            FStar_Util.bind_opt uu____2725
                              (fun c  ->
                                 let uu____2731 =
                                   let uu____2732 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____2732  in
                                 FStar_Pervasives_Native.Some uu____2731)))
              | uu____2733 -> FStar_Pervasives_Native.None
  