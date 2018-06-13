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
    let uu___199_418 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___199_418.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___199_418.FStar_Syntax_Syntax.vars)
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
    let uu___200_466 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___200_466.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___200_466.FStar_Syntax_Syntax.vars)
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
    let uu___201_515 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___201_515.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___201_515.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____540 ->
        (if w
         then
           (let uu____542 =
              let uu____547 =
                let uu____548 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____548  in
              (FStar_Errors.Warning_NotEmbedded, uu____547)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____542)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let em rng i =
    let t =
      let uu____566 = FStar_BigInt.string_of_big_int i  in
      FStar_Syntax_Util.exp_int uu____566  in
    let uu___202_567 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___202_567.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___202_567.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____587))
        ->
        let uu____600 = FStar_BigInt.big_int_of_string s  in
        FStar_Pervasives_Native.Some uu____600
    | uu____601 ->
        (if w
         then
           (let uu____603 =
              let uu____608 =
                let uu____609 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded int: %s" uu____609  in
              (FStar_Errors.Warning_NotEmbedded, uu____608)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____603)
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
        (s,uu____643)) -> FStar_Pervasives_Native.Some s
    | uu____644 ->
        (if w
         then
           (let uu____646 =
              let uu____651 =
                let uu____652 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____652  in
              (FStar_Errors.Warning_NotEmbedded, uu____651)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____646)
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
          let uu____687 =
            let uu____692 =
              let uu____693 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____693
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____694 =
              let uu____695 =
                let uu____702 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____702  in
              [uu____695]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____692 uu____694  in
          uu____687 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____718 =
            let uu____723 =
              let uu____724 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____724
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____725 =
              let uu____726 =
                let uu____733 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____733  in
              let uu____734 =
                let uu____743 =
                  let uu____750 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____750  in
                [uu____743]  in
              uu____726 :: uu____734  in
            FStar_Syntax_Syntax.mk_Tm_app uu____723 uu____725  in
          uu____718 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____791 = FStar_Syntax_Util.head_and_args t  in
      match uu____791 with
      | (hd1,args) ->
          let uu____832 =
            let uu____845 =
              let uu____846 = FStar_Syntax_Util.un_uinst hd1  in
              uu____846.FStar_Syntax_Syntax.n  in
            (uu____845, args)  in
          (match uu____832 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____862) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____882::(a,uu____884)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____921 = unembed' w ea a  in
               FStar_Util.bind_opt uu____921
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____930 ->
               (if w
                then
                  (let uu____944 =
                     let uu____949 =
                       let uu____950 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____950
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____949)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____944)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____954 =
      let uu____955 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____955  in
    mk_emb em un uu____954
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____1011 =
          let uu____1016 =
            let uu____1017 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1017
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____1018 =
            let uu____1019 =
              let uu____1026 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1026  in
            let uu____1027 =
              let uu____1036 =
                let uu____1043 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____1043  in
              let uu____1044 =
                let uu____1053 =
                  let uu____1060 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____1060  in
                let uu____1061 =
                  let uu____1070 =
                    let uu____1077 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____1077  in
                  [uu____1070]  in
                uu____1053 :: uu____1061  in
              uu____1036 :: uu____1044  in
            uu____1019 :: uu____1027  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1016 uu____1018  in
        uu____1011 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1134 = FStar_Syntax_Util.head_and_args t  in
        match uu____1134 with
        | (hd1,args) ->
            let uu____1177 =
              let uu____1188 =
                let uu____1189 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1189.FStar_Syntax_Syntax.n  in
              (uu____1188, args)  in
            (match uu____1177 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1205::uu____1206::(a,uu____1208)::(b,uu____1210)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1245 = unembed' w ea a  in
                 FStar_Util.bind_opt uu____1245
                   (fun a1  ->
                      let uu____1255 = unembed' w eb b  in
                      FStar_Util.bind_opt uu____1255
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1268 ->
                 (if w
                  then
                    (let uu____1280 =
                       let uu____1285 =
                         let uu____1286 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1286
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1285)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1280)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1292 =
        let uu____1293 = type_of ea  in
        let uu____1294 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1293 uu____1294  in
      mk_emb em un uu____1292
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1333 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1333
         in
      let nil =
        let uu____1337 =
          let uu____1342 =
            let uu____1343 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1343
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1342 [t]  in
        uu____1337 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1359 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1359
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1367 =
               let uu____1372 =
                 let uu____1373 =
                   let uu____1382 =
                     let uu____1389 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1389  in
                   let uu____1390 =
                     let uu____1399 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1399]  in
                   uu____1382 :: uu____1390  in
                 t :: uu____1373  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1372  in
             uu____1367 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1452 = FStar_Syntax_Util.head_and_args t  in
      match uu____1452 with
      | (hd1,args) ->
          let uu____1493 =
            let uu____1506 =
              let uu____1507 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1507.FStar_Syntax_Syntax.n  in
            (uu____1506, args)  in
          (match uu____1493 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1523) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(uu____1543,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit uu____1544))::(hd2,FStar_Pervasives_Native.None
                                                               )::(tl1,FStar_Pervasives_Native.None
                                                                   )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1585 = unembed' w ea hd2  in
               FStar_Util.bind_opt uu____1585
                 (fun hd3  ->
                    let uu____1593 = un w tl1  in
                    FStar_Util.bind_opt uu____1593
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                       )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1641 = unembed' w ea hd2  in
               FStar_Util.bind_opt uu____1641
                 (fun hd3  ->
                    let uu____1649 = un w tl1  in
                    FStar_Util.bind_opt uu____1649
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1664 ->
               (if w
                then
                  (let uu____1678 =
                     let uu____1683 =
                       let uu____1684 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1684
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1683)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1678)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1688 =
      let uu____1689 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1689  in
    mk_emb em un uu____1688
  
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
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____1720 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1726 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1732 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1738 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1744 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1750 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1756 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1765 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1787 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1807 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____1820 -> false 
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
let (steps_NBE : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_nbe 
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
        let uu____1837 =
          let uu____1842 =
            let uu____1843 =
              let uu____1850 =
                let uu____1851 = e_list e_string  in embed uu____1851 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1850  in
            [uu____1843]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1842  in
        uu____1837 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____1875 =
          let uu____1880 =
            let uu____1881 =
              let uu____1888 =
                let uu____1889 = e_list e_string  in embed uu____1889 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1888  in
            [uu____1881]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____1880  in
        uu____1875 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____1911 =
          let uu____1916 =
            let uu____1917 = FStar_Syntax_Syntax.as_arg a  in [uu____1917]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1916  in
        uu____1911 FStar_Pervasives_Native.None rng
    | NBE  -> steps_NBE  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____1954 = FStar_Syntax_Util.head_and_args t  in
    match uu____1954 with
    | (hd1,args) ->
        let uu____1993 =
          let uu____2006 =
            let uu____2007 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2007.FStar_Syntax_Syntax.n  in
          (uu____2006, args)  in
        (match uu____1993 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
             FStar_Pervasives_Native.Some NBE
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2142)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____2167 =
               let uu____2172 = e_list e_string  in unembed' w uu____2172 l
                in
             FStar_Util.bind_opt uu____2167
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2189)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____2214 =
               let uu____2219 = e_list e_string  in unembed' w uu____2219 l
                in
             FStar_Util.bind_opt uu____2214
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2235::(a,uu____2237)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____2274 ->
             (if w
              then
                (let uu____2288 =
                   let uu____2293 =
                     let uu____2294 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____2294
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2293)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2288)
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
    | uu____2328 ->
        (if w
         then
           (let uu____2330 =
              let uu____2335 =
                let uu____2336 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____2336  in
              (FStar_Errors.Warning_NotEmbedded, uu____2335)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2330)
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
          | (x,uu____2406)::[] ->
              let uu____2423 = ua x  in
              FStar_Util.bind_opt uu____2423
                (fun a  ->
                   let uu____2429 =
                     let uu____2430 =
                       let uu____2431 =
                         let uu____2432 = ua x  in FStar_Util.must uu____2432
                          in
                       f uu____2431  in
                     eb1 FStar_Range.dummyRange uu____2430  in
                   FStar_Pervasives_Native.Some uu____2429)
          | uu____2435 -> FStar_Pervasives_Native.None
  
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
            | (x,uu____2530)::(y,uu____2532)::[] ->
                let uu____2559 = ua x  in
                FStar_Util.bind_opt uu____2559
                  (fun a  ->
                     let uu____2565 = ub y  in
                     FStar_Util.bind_opt uu____2565
                       (fun b  ->
                          let uu____2571 =
                            let uu____2572 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2572  in
                          FStar_Pervasives_Native.Some uu____2571))
            | uu____2573 -> FStar_Pervasives_Native.None
  
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
              | (x,uu____2694)::(y,uu____2696)::(z,uu____2698)::[] ->
                  let uu____2735 = ua x  in
                  FStar_Util.bind_opt uu____2735
                    (fun a  ->
                       let uu____2741 = ub y  in
                       FStar_Util.bind_opt uu____2741
                         (fun b  ->
                            let uu____2747 = uc z  in
                            FStar_Util.bind_opt uu____2747
                              (fun c  ->
                                 let uu____2753 =
                                   let uu____2754 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____2754  in
                                 FStar_Pervasives_Native.Some uu____2753)))
              | uu____2755 -> FStar_Pervasives_Native.None
  