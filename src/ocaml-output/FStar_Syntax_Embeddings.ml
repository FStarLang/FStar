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
    let uu___50_400 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___50_400.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___50_400.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____419 ->
        let uu____420 =
          if w
          then
            let uu____421 =
              let uu____426 =
                let uu____427 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____427  in
              (FStar_Errors.Warning_NotEmbedded, uu____426)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____421
          else ()  in
        FStar_Pervasives_Native.None
     in
  mk_emb em un FStar_Syntax_Syntax.t_unit 
let (e_bool : Prims.bool embedding) =
  let em rng b =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___51_446 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___51_446.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___51_446.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____466 ->
        let uu____467 =
          if w
          then
            let uu____468 =
              let uu____473 =
                let uu____474 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____474  in
              (FStar_Errors.Warning_NotEmbedded, uu____473)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____468
          else ()  in
        FStar_Pervasives_Native.None
     in
  mk_emb em un FStar_Syntax_Syntax.t_bool 
let (e_char : FStar_Char.char embedding) =
  let em rng c =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___52_491 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___52_491.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___52_491.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____512 ->
        let uu____513 =
          if w
          then
            let uu____514 =
              let uu____519 =
                let uu____520 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____520  in
              (FStar_Errors.Warning_NotEmbedded, uu____519)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____514
          else ()  in
        FStar_Pervasives_Native.None
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let em rng i =
    let t =
      let uu____536 = FStar_BigInt.string_of_big_int i  in
      FStar_Syntax_Util.exp_int uu____536  in
    let uu___53_537 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___53_537.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___53_537.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____555))
        ->
        let uu____568 = FStar_BigInt.big_int_of_string s  in
        FStar_Pervasives_Native.Some uu____568
    | uu____569 ->
        let uu____570 =
          if w
          then
            let uu____571 =
              let uu____576 =
                let uu____577 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded int: %s" uu____577  in
              (FStar_Errors.Warning_NotEmbedded, uu____576)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____571
          else ()  in
        FStar_Pervasives_Native.None
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
        (s,uu____607)) -> FStar_Pervasives_Native.Some s
    | uu____608 ->
        let uu____609 =
          if w
          then
            let uu____610 =
              let uu____615 =
                let uu____616 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____616  in
              (FStar_Errors.Warning_NotEmbedded, uu____615)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____610
          else ()  in
        FStar_Pervasives_Native.None
     in
  mk_emb em un FStar_Syntax_Syntax.t_string 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em rng o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____649 =
            let uu____652 =
              let uu____653 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____653
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____654 =
              let uu____655 =
                let uu____656 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____656  in
              [uu____655]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____652 uu____654  in
          uu____649 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____660 =
            let uu____663 =
              let uu____664 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____664
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____665 =
              let uu____666 =
                let uu____667 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____667  in
              let uu____668 =
                let uu____671 =
                  let uu____672 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____672  in
                [uu____671]  in
              uu____666 :: uu____668  in
            FStar_Syntax_Syntax.mk_Tm_app uu____663 uu____665  in
          uu____660 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____693 = FStar_Syntax_Util.head_and_args t  in
      match uu____693 with
      | (hd1,args) ->
          let uu____734 =
            let uu____747 =
              let uu____748 = FStar_Syntax_Util.un_uinst hd1  in
              uu____748.FStar_Syntax_Syntax.n  in
            (uu____747, args)  in
          (match uu____734 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____764) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____784::(a,uu____786)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____823 = unembed ea a  in
               FStar_Util.bind_opt uu____823
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____832 ->
               let uu____845 =
                 if w
                 then
                   let uu____846 =
                     let uu____851 =
                       let uu____852 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____852
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____851)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____846
                 else ()  in
               FStar_Pervasives_Native.None)
       in
    let uu____856 =
      let uu____857 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____857  in
    mk_emb em un uu____856
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____911 =
          let uu____914 =
            let uu____915 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____915
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____916 =
            let uu____917 =
              let uu____918 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____918  in
            let uu____919 =
              let uu____922 =
                let uu____923 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____923  in
              let uu____924 =
                let uu____927 =
                  let uu____928 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____928  in
                let uu____929 =
                  let uu____932 =
                    let uu____933 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____933  in
                  [uu____932]  in
                uu____927 :: uu____929  in
              uu____922 :: uu____924  in
            uu____917 :: uu____919  in
          FStar_Syntax_Syntax.mk_Tm_app uu____914 uu____916  in
        uu____911 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____958 = FStar_Syntax_Util.head_and_args t  in
        match uu____958 with
        | (hd1,args) ->
            let uu____1001 =
              let uu____1014 =
                let uu____1015 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1015.FStar_Syntax_Syntax.n  in
              (uu____1014, args)  in
            (match uu____1001 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1033::uu____1034::(a,uu____1036)::(b,uu____1038)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1097 = unembed ea a  in
                 FStar_Util.bind_opt uu____1097
                   (fun a1  ->
                      let uu____1107 = unembed eb b  in
                      FStar_Util.bind_opt uu____1107
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1120 ->
                 let uu____1133 =
                   if w
                   then
                     let uu____1134 =
                       let uu____1139 =
                         let uu____1140 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1140
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1139)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1134
                   else ()  in
                 FStar_Pervasives_Native.None)
         in
      let uu____1146 =
        let uu____1147 = type_of ea  in
        let uu____1148 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1147 uu____1148  in
      mk_emb em un uu____1146
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1185 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1185
         in
      let nil =
        let uu____1189 =
          let uu____1192 =
            let uu____1193 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1193
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1192 [t]  in
        uu____1189 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1197 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1197
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1205 =
               let uu____1208 =
                 let uu____1209 =
                   let uu____1212 =
                     let uu____1213 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1213  in
                   let uu____1214 =
                     let uu____1217 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1217]  in
                   uu____1212 :: uu____1214  in
                 t :: uu____1209  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1208  in
             uu____1205 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1238 = FStar_Syntax_Util.head_and_args t  in
      match uu____1238 with
      | (hd1,args) ->
          let uu____1279 =
            let uu____1292 =
              let uu____1293 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1293.FStar_Syntax_Syntax.n  in
            (uu____1292, args)  in
          (match uu____1279 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1309) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,_t::(hd2,uu____1331)::(tl1,uu____1333)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1380 = unembed ea hd2  in
               FStar_Util.bind_opt uu____1380
                 (fun hd3  ->
                    let uu____1388 = un w tl1  in
                    FStar_Util.bind_opt uu____1388
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1403 ->
               let uu____1416 =
                 if w
                 then
                   let uu____1417 =
                     let uu____1422 =
                       let uu____1423 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1423
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1422)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1417
                 else ()  in
               FStar_Pervasives_Native.None)
       in
    let uu____1427 =
      let uu____1428 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1428  in
    mk_emb em un uu____1427
  
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
    match projectee with | Simpl  -> true | uu____1456 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1462 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1468 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1474 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1480 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1486 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1492 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1501 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1523 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1543 -> false
  
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
        let uu____1565 =
          let uu____1568 =
            let uu____1569 =
              let uu____1570 =
                let uu____1571 = e_list e_string  in embed uu____1571 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1570  in
            [uu____1569]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1568  in
        uu____1565 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____1583 =
          let uu____1586 =
            let uu____1587 =
              let uu____1588 =
                let uu____1589 = e_list e_string  in embed uu____1589 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1588  in
            [uu____1587]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____1586  in
        uu____1583 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____1599 =
          let uu____1602 =
            let uu____1603 = FStar_Syntax_Syntax.as_arg a  in [uu____1603]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1602  in
        uu____1599 FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____1620 = FStar_Syntax_Util.head_and_args t  in
    match uu____1620 with
    | (hd1,args) ->
        let uu____1659 =
          let uu____1672 =
            let uu____1673 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1673.FStar_Syntax_Syntax.n  in
          (uu____1672, args)  in
        (match uu____1659 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1793)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____1818 =
               let uu____1823 = e_list e_string  in unembed uu____1823 l  in
             FStar_Util.bind_opt uu____1818
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1840)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____1865 =
               let uu____1870 = e_list e_string  in unembed uu____1870 l  in
             FStar_Util.bind_opt uu____1865
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1886::(a,uu____1888)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____1925 ->
             let uu____1938 =
               if w
               then
                 let uu____1939 =
                   let uu____1944 =
                     let uu____1945 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____1945
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1944)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1939
               else ()  in
             FStar_Pervasives_Native.None)
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
    | uu____1975 ->
        let uu____1976 =
          if w
          then
            let uu____1977 =
              let uu____1982 =
                let uu____1983 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____1983  in
              (FStar_Errors.Warning_NotEmbedded, uu____1982)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1977
          else ()  in
        FStar_Pervasives_Native.None
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
          | (x,uu____2050)::[] ->
              let uu____2067 = ua x  in
              FStar_Util.bind_opt uu____2067
                (fun a  ->
                   let uu____2073 =
                     let uu____2074 =
                       let uu____2075 =
                         let uu____2076 = ua x  in FStar_Util.must uu____2076
                          in
                       f uu____2075  in
                     eb1 FStar_Range.dummyRange uu____2074  in
                   FStar_Pervasives_Native.Some uu____2073)
          | uu____2079 -> FStar_Pervasives_Native.None
  
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
            | (x,uu____2170)::(y,uu____2172)::[] ->
                let uu____2199 = ua x  in
                FStar_Util.bind_opt uu____2199
                  (fun a  ->
                     let uu____2205 = ub y  in
                     FStar_Util.bind_opt uu____2205
                       (fun b  ->
                          let uu____2211 =
                            let uu____2212 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2212  in
                          FStar_Pervasives_Native.Some uu____2211))
            | uu____2213 -> FStar_Pervasives_Native.None
  
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
              | (x,uu____2329)::(y,uu____2331)::(z,uu____2333)::[] ->
                  let uu____2370 = ua x  in
                  FStar_Util.bind_opt uu____2370
                    (fun a  ->
                       let uu____2376 = ub y  in
                       FStar_Util.bind_opt uu____2376
                         (fun b  ->
                            let uu____2382 = uc z  in
                            FStar_Util.bind_opt uu____2382
                              (fun c  ->
                                 let uu____2388 =
                                   let uu____2389 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____2389  in
                                 FStar_Pervasives_Native.Some uu____2388)))
              | uu____2390 -> FStar_Pervasives_Native.None
  