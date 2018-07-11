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
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___202_294 = e  in
      { em = (uu___202_294.em); un = (uu___202_294.un); typ = ty }
  
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
    let uu___203_444 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___203_444.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___203_444.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____463 ->
        (if w
         then
           (let uu____465 =
              let uu____470 =
                let uu____471 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____471  in
              (FStar_Errors.Warning_NotEmbedded, uu____470)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____465)
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
    let uu___204_492 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___204_492.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___204_492.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____514 ->
        (if w
         then
           (let uu____516 =
              let uu____521 =
                let uu____522 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____522  in
              (FStar_Errors.Warning_NotEmbedded, uu____521)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____516)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_bool 
let (e_char : FStar_Char.char embedding) =
  let em rng c =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___205_541 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___205_541.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___205_541.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____566 ->
        (if w
         then
           (let uu____568 =
              let uu____573 =
                let uu____574 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____574  in
              (FStar_Errors.Warning_NotEmbedded, uu____573)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____568)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let em rng i =
    let t =
      let uu____592 = FStar_BigInt.string_of_big_int i  in
      FStar_Syntax_Util.exp_int uu____592  in
    let uu___206_593 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___206_593.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___206_593.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____613))
        ->
        let uu____626 = FStar_BigInt.big_int_of_string s  in
        FStar_Pervasives_Native.Some uu____626
    | uu____627 ->
        (if w
         then
           (let uu____629 =
              let uu____634 =
                let uu____635 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded int: %s" uu____635  in
              (FStar_Errors.Warning_NotEmbedded, uu____634)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____629)
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
        (s,uu____669)) -> FStar_Pervasives_Native.Some s
    | uu____670 ->
        (if w
         then
           (let uu____672 =
              let uu____677 =
                let uu____678 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____678  in
              (FStar_Errors.Warning_NotEmbedded, uu____677)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____672)
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
          let uu____713 =
            let uu____718 =
              let uu____719 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____719
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____720 =
              let uu____721 =
                let uu____730 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____730  in
              [uu____721]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____718 uu____720  in
          uu____713 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____750 =
            let uu____755 =
              let uu____756 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____756
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____757 =
              let uu____758 =
                let uu____767 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____767  in
              let uu____768 =
                let uu____779 =
                  let uu____788 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____788  in
                [uu____779]  in
              uu____758 :: uu____768  in
            FStar_Syntax_Syntax.mk_Tm_app uu____755 uu____757  in
          uu____750 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____835 = FStar_Syntax_Util.head_and_args' t  in
      match uu____835 with
      | (hd1,args) ->
          let uu____876 =
            let uu____891 =
              let uu____892 = FStar_Syntax_Util.un_uinst hd1  in
              uu____892.FStar_Syntax_Syntax.n  in
            (uu____891, args)  in
          (match uu____876 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____910) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____934::(a,uu____936)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____987 = unembed' w ea a  in
               FStar_Util.bind_opt uu____987
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____996 ->
               (if w
                then
                  (let uu____1012 =
                     let uu____1017 =
                       let uu____1018 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____1018
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1017)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1012)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1022 =
      let uu____1023 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____1023  in
    mk_emb em un uu____1022
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____1079 =
          let uu____1084 =
            let uu____1085 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1085
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____1086 =
            let uu____1087 =
              let uu____1096 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1096  in
            let uu____1097 =
              let uu____1108 =
                let uu____1117 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____1117  in
              let uu____1118 =
                let uu____1129 =
                  let uu____1138 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____1138  in
                let uu____1139 =
                  let uu____1150 =
                    let uu____1159 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____1159  in
                  [uu____1150]  in
                uu____1129 :: uu____1139  in
              uu____1108 :: uu____1118  in
            uu____1087 :: uu____1097  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1084 uu____1086  in
        uu____1079 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1226 = FStar_Syntax_Util.head_and_args' t  in
        match uu____1226 with
        | (hd1,args) ->
            let uu____1269 =
              let uu____1282 =
                let uu____1283 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1283.FStar_Syntax_Syntax.n  in
              (uu____1282, args)  in
            (match uu____1269 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1301::uu____1302::(a,uu____1304)::(b,uu____1306)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1365 = unembed' w ea a  in
                 FStar_Util.bind_opt uu____1365
                   (fun a1  ->
                      let uu____1375 = unembed' w eb b  in
                      FStar_Util.bind_opt uu____1375
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1388 ->
                 (if w
                  then
                    (let uu____1402 =
                       let uu____1407 =
                         let uu____1408 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1408
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1407)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1402)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1414 =
        let uu____1415 = type_of ea  in
        let uu____1416 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1415 uu____1416  in
      mk_emb em un uu____1414
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng s =
        match s with
        | FStar_Util.Inl a ->
            let uu____1475 =
              let uu____1480 =
                let uu____1481 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.inl_lid
                   in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____1481
                  [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                 in
              let uu____1482 =
                let uu____1483 =
                  let uu____1492 = type_of ea  in
                  FStar_Syntax_Syntax.iarg uu____1492  in
                let uu____1493 =
                  let uu____1504 =
                    let uu____1513 = type_of eb  in
                    FStar_Syntax_Syntax.iarg uu____1513  in
                  let uu____1514 =
                    let uu____1525 =
                      let uu____1534 = embed ea rng a  in
                      FStar_Syntax_Syntax.as_arg uu____1534  in
                    [uu____1525]  in
                  uu____1504 :: uu____1514  in
                uu____1483 :: uu____1493  in
              FStar_Syntax_Syntax.mk_Tm_app uu____1480 uu____1482  in
            uu____1475 FStar_Pervasives_Native.None rng
        | FStar_Util.Inr b ->
            let uu____1570 =
              let uu____1575 =
                let uu____1576 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.inr_lid
                   in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____1576
                  [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                 in
              let uu____1577 =
                let uu____1578 =
                  let uu____1587 = type_of ea  in
                  FStar_Syntax_Syntax.iarg uu____1587  in
                let uu____1588 =
                  let uu____1599 =
                    let uu____1608 = type_of eb  in
                    FStar_Syntax_Syntax.iarg uu____1608  in
                  let uu____1609 =
                    let uu____1620 =
                      let uu____1629 = embed eb rng b  in
                      FStar_Syntax_Syntax.as_arg uu____1629  in
                    [uu____1620]  in
                  uu____1599 :: uu____1609  in
                uu____1578 :: uu____1588  in
              FStar_Syntax_Syntax.mk_Tm_app uu____1575 uu____1577  in
            uu____1570 FStar_Pervasives_Native.None rng
         in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1688 = FStar_Syntax_Util.head_and_args' t  in
        match uu____1688 with
        | (hd1,args) ->
            let uu____1731 =
              let uu____1746 =
                let uu____1747 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1747.FStar_Syntax_Syntax.n  in
              (uu____1746, args)  in
            (match uu____1731 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1767::(a,uu____1769)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.inl_lid
                 ->
                 let uu____1820 = unembed' w ea a  in
                 FStar_Util.bind_opt uu____1820
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1834::(b,uu____1836)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.inr_lid
                 ->
                 let uu____1887 = unembed' w eb b  in
                 FStar_Util.bind_opt uu____1887
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____1900 ->
                 (if w
                  then
                    (let uu____1916 =
                       let uu____1921 =
                         let uu____1922 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded sum: %s"
                           uu____1922
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1921)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1916)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1928 =
        let uu____1929 = type_of ea  in
        let uu____1930 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____1929 uu____1930  in
      mk_emb em un uu____1928
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1969 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1969
         in
      let nil =
        let uu____1973 =
          let uu____1978 =
            let uu____1979 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1979
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1978 [t]  in
        uu____1973 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1999 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1999
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____2007 =
               let uu____2012 =
                 let uu____2013 =
                   let uu____2024 =
                     let uu____2033 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____2033  in
                   let uu____2034 =
                     let uu____2045 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____2045]  in
                   uu____2024 :: uu____2034  in
                 t :: uu____2013  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____2012  in
             uu____2007 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____2108 = FStar_Syntax_Util.head_and_args' t  in
      match uu____2108 with
      | (hd1,args) ->
          let uu____2149 =
            let uu____2162 =
              let uu____2163 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2163.FStar_Syntax_Syntax.n  in
            (uu____2162, args)  in
          (match uu____2149 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2179) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(uu____2199,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit uu____2200))::(hd2,FStar_Pervasives_Native.None
                                                               )::(tl1,FStar_Pervasives_Native.None
                                                                   )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____2241 = unembed' w ea hd2  in
               FStar_Util.bind_opt uu____2241
                 (fun hd3  ->
                    let uu____2249 = un w tl1  in
                    FStar_Util.bind_opt uu____2249
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                       )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____2297 = unembed' w ea hd2  in
               FStar_Util.bind_opt uu____2297
                 (fun hd3  ->
                    let uu____2305 = un w tl1  in
                    FStar_Util.bind_opt uu____2305
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____2320 ->
               (if w
                then
                  (let uu____2334 =
                     let uu____2339 =
                       let uu____2340 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____2340
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2339)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____2334)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____2344 =
      let uu____2345 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____2345  in
    mk_emb em un uu____2344
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | Iota 
  | Reify 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____2376 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____2382 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____2388 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____2394 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____2400 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____2406 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____2412 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____2418 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____2427 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____2449 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____2469 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____2482 -> false 
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
let (steps_Reify : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_reify 
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
    | Reify  -> steps_Reify
    | UnfoldOnly l ->
        let uu____2499 =
          let uu____2504 =
            let uu____2505 =
              let uu____2514 =
                let uu____2515 = e_list e_string  in embed uu____2515 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____2514  in
            [uu____2505]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____2504  in
        uu____2499 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____2543 =
          let uu____2548 =
            let uu____2549 =
              let uu____2558 =
                let uu____2559 = e_list e_string  in embed uu____2559 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____2558  in
            [uu____2549]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____2548  in
        uu____2543 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____2585 =
          let uu____2590 =
            let uu____2591 = FStar_Syntax_Syntax.as_arg a  in [uu____2591]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____2590  in
        uu____2585 FStar_Pervasives_Native.None rng
    | NBE  -> steps_NBE  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____2634 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2634 with
    | (hd1,args) ->
        let uu____2673 =
          let uu____2688 =
            let uu____2689 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2689.FStar_Syntax_Syntax.n  in
          (uu____2688, args)  in
        (match uu____2673 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify
             -> FStar_Pervasives_Native.Some Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2877)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____2912 =
               let uu____2917 = e_list e_string  in unembed' w uu____2917 l
                in
             FStar_Util.bind_opt uu____2912
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2934)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____2969 =
               let uu____2974 = e_list e_string  in unembed' w uu____2974 l
                in
             FStar_Util.bind_opt uu____2969
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2990::(a,uu____2992)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____3043 ->
             (if w
              then
                (let uu____3059 =
                   let uu____3064 =
                     let uu____3065 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____3065
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3064)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____3059)
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
    | uu____3099 ->
        (if w
         then
           (let uu____3101 =
              let uu____3106 =
                let uu____3107 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____3107  in
              (FStar_Errors.Warning_NotEmbedded, uu____3106)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____3101)
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
          | (x,uu____3177)::[] ->
              let uu____3202 = ua x  in
              FStar_Util.bind_opt uu____3202
                (fun a  ->
                   let uu____3208 =
                     let uu____3209 =
                       let uu____3210 =
                         let uu____3211 = ua x  in FStar_Util.must uu____3211
                          in
                       f uu____3210  in
                     eb1 FStar_Range.dummyRange uu____3209  in
                   FStar_Pervasives_Native.Some uu____3208)
          | uu____3214 -> FStar_Pervasives_Native.None
  
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
            | (x,uu____3309)::(y,uu____3311)::[] ->
                let uu____3352 = ua x  in
                FStar_Util.bind_opt uu____3352
                  (fun a  ->
                     let uu____3358 = ub y  in
                     FStar_Util.bind_opt uu____3358
                       (fun b  ->
                          let uu____3364 =
                            let uu____3365 = f a b  in
                            ec1 FStar_Range.dummyRange uu____3365  in
                          FStar_Pervasives_Native.Some uu____3364))
            | uu____3366 -> FStar_Pervasives_Native.None
  
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
              | (x,uu____3487)::(y,uu____3489)::(z,uu____3491)::[] ->
                  let uu____3548 = ua x  in
                  FStar_Util.bind_opt uu____3548
                    (fun a  ->
                       let uu____3554 = ub y  in
                       FStar_Util.bind_opt uu____3554
                         (fun b  ->
                            let uu____3560 = uc z  in
                            FStar_Util.bind_opt uu____3560
                              (fun c  ->
                                 let uu____3566 =
                                   let uu____3567 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____3567  in
                                 FStar_Pervasives_Native.Some uu____3566)))
              | uu____3568 -> FStar_Pervasives_Native.None
  