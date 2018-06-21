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
    let uu___201_418 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___201_418.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___201_418.FStar_Syntax_Syntax.vars)
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
    let uu___202_466 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___202_466.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___202_466.FStar_Syntax_Syntax.vars)
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
    let uu___203_515 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___203_515.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___203_515.FStar_Syntax_Syntax.vars)
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
    let uu___204_567 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___204_567.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___204_567.FStar_Syntax_Syntax.vars)
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
                let uu____704 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____704  in
              [uu____695]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____692 uu____694  in
          uu____687 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____724 =
            let uu____729 =
              let uu____730 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____730
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____731 =
              let uu____732 =
                let uu____741 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____741  in
              let uu____742 =
                let uu____753 =
                  let uu____762 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____762  in
                [uu____753]  in
              uu____732 :: uu____742  in
            FStar_Syntax_Syntax.mk_Tm_app uu____729 uu____731  in
          uu____724 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____809 = FStar_Syntax_Util.head_and_args t  in
      match uu____809 with
      | (hd1,args) ->
          let uu____856 =
            let uu____871 =
              let uu____872 = FStar_Syntax_Util.un_uinst hd1  in
              uu____872.FStar_Syntax_Syntax.n  in
            (uu____871, args)  in
          (match uu____856 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____890) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____914::(a,uu____916)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____967 = unembed' w ea a  in
               FStar_Util.bind_opt uu____967
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____976 ->
               (if w
                then
                  (let uu____992 =
                     let uu____997 =
                       let uu____998 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____998
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____997)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____992)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1002 =
      let uu____1003 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____1003  in
    mk_emb em un uu____1002
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____1059 =
          let uu____1064 =
            let uu____1065 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1065
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____1066 =
            let uu____1067 =
              let uu____1076 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1076  in
            let uu____1077 =
              let uu____1088 =
                let uu____1097 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____1097  in
              let uu____1098 =
                let uu____1109 =
                  let uu____1118 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____1118  in
                let uu____1119 =
                  let uu____1130 =
                    let uu____1139 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____1139  in
                  [uu____1130]  in
                uu____1109 :: uu____1119  in
              uu____1088 :: uu____1098  in
            uu____1067 :: uu____1077  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1064 uu____1066  in
        uu____1059 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1206 = FStar_Syntax_Util.head_and_args t  in
        match uu____1206 with
        | (hd1,args) ->
            let uu____1255 =
              let uu____1268 =
                let uu____1269 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1269.FStar_Syntax_Syntax.n  in
              (uu____1268, args)  in
            (match uu____1255 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1287::uu____1288::(a,uu____1290)::(b,uu____1292)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1351 = unembed' w ea a  in
                 FStar_Util.bind_opt uu____1351
                   (fun a1  ->
                      let uu____1361 = unembed' w eb b  in
                      FStar_Util.bind_opt uu____1361
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1374 ->
                 (if w
                  then
                    (let uu____1388 =
                       let uu____1393 =
                         let uu____1394 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1394
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1393)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1388)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1400 =
        let uu____1401 = type_of ea  in
        let uu____1402 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1401 uu____1402  in
      mk_emb em un uu____1400
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1441 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1441
         in
      let nil =
        let uu____1445 =
          let uu____1450 =
            let uu____1451 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1451
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1450 [t]  in
        uu____1445 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1471 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1471
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1479 =
               let uu____1484 =
                 let uu____1485 =
                   let uu____1496 =
                     let uu____1505 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1505  in
                   let uu____1506 =
                     let uu____1517 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1517]  in
                   uu____1496 :: uu____1506  in
                 t :: uu____1485  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1484  in
             uu____1479 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1580 = FStar_Syntax_Util.head_and_args t  in
      match uu____1580 with
      | (hd1,args) ->
          let uu____1627 =
            let uu____1640 =
              let uu____1641 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1641.FStar_Syntax_Syntax.n  in
            (uu____1640, args)  in
          (match uu____1627 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1657) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(uu____1677,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit uu____1678))::(hd2,FStar_Pervasives_Native.None
                                                               )::(tl1,FStar_Pervasives_Native.None
                                                                   )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1719 = unembed' w ea hd2  in
               FStar_Util.bind_opt uu____1719
                 (fun hd3  ->
                    let uu____1727 = un w tl1  in
                    FStar_Util.bind_opt uu____1727
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                       )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1775 = unembed' w ea hd2  in
               FStar_Util.bind_opt uu____1775
                 (fun hd3  ->
                    let uu____1783 = un w tl1  in
                    FStar_Util.bind_opt uu____1783
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1798 ->
               (if w
                then
                  (let uu____1812 =
                     let uu____1817 =
                       let uu____1818 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1818
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1817)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1812)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1822 =
      let uu____1823 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1823  in
    mk_emb em un uu____1822
  
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
    match projectee with | Simpl  -> true | uu____1854 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1860 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1866 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1872 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1878 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1884 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1890 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1899 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1921 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1941 -> false
  
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
        let uu____1965 =
          let uu____1970 =
            let uu____1971 =
              let uu____1980 =
                let uu____1981 = e_list e_string  in embed uu____1981 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1980  in
            [uu____1971]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1970  in
        uu____1965 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____2009 =
          let uu____2014 =
            let uu____2015 =
              let uu____2024 =
                let uu____2025 = e_list e_string  in embed uu____2025 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____2024  in
            [uu____2015]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____2014  in
        uu____2009 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____2051 =
          let uu____2056 =
            let uu____2057 = FStar_Syntax_Syntax.as_arg a  in [uu____2057]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____2056  in
        uu____2051 FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____2100 = FStar_Syntax_Util.head_and_args t  in
    match uu____2100 with
    | (hd1,args) ->
        let uu____2145 =
          let uu____2160 =
            let uu____2161 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2161.FStar_Syntax_Syntax.n  in
          (uu____2160, args)  in
        (match uu____2145 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2311)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____2346 =
               let uu____2351 = e_list e_string  in unembed' w uu____2351 l
                in
             FStar_Util.bind_opt uu____2346
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2368)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____2403 =
               let uu____2408 = e_list e_string  in unembed' w uu____2408 l
                in
             FStar_Util.bind_opt uu____2403
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2424::(a,uu____2426)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____2477 ->
             (if w
              then
                (let uu____2493 =
                   let uu____2498 =
                     let uu____2499 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____2499
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2498)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2493)
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
    | uu____2533 ->
        (if w
         then
           (let uu____2535 =
              let uu____2540 =
                let uu____2541 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____2541  in
              (FStar_Errors.Warning_NotEmbedded, uu____2540)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2535)
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
          | (x,uu____2611)::[] ->
              let uu____2636 = ua x  in
              FStar_Util.bind_opt uu____2636
                (fun a  ->
                   let uu____2642 =
                     let uu____2643 =
                       let uu____2644 =
                         let uu____2645 = ua x  in FStar_Util.must uu____2645
                          in
                       f uu____2644  in
                     eb1 FStar_Range.dummyRange uu____2643  in
                   FStar_Pervasives_Native.Some uu____2642)
          | uu____2648 -> FStar_Pervasives_Native.None
  
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
            | (x,uu____2743)::(y,uu____2745)::[] ->
                let uu____2786 = ua x  in
                FStar_Util.bind_opt uu____2786
                  (fun a  ->
                     let uu____2792 = ub y  in
                     FStar_Util.bind_opt uu____2792
                       (fun b  ->
                          let uu____2798 =
                            let uu____2799 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2799  in
                          FStar_Pervasives_Native.Some uu____2798))
            | uu____2800 -> FStar_Pervasives_Native.None
  
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
              | (x,uu____2921)::(y,uu____2923)::(z,uu____2925)::[] ->
                  let uu____2982 = ua x  in
                  FStar_Util.bind_opt uu____2982
                    (fun a  ->
                       let uu____2988 = ub y  in
                       FStar_Util.bind_opt uu____2988
                         (fun b  ->
                            let uu____2994 = uc z  in
                            FStar_Util.bind_opt uu____2994
                              (fun c  ->
                                 let uu____3000 =
                                   let uu____3001 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____3001  in
                                 FStar_Pervasives_Native.Some uu____3000)))
              | uu____3002 -> FStar_Pervasives_Native.None
  