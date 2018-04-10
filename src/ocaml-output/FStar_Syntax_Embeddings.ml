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
    let uu___50_406 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___50_406.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___50_406.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____427 ->
        let uu____428 =
          if w
          then
            let uu____429 =
              let uu____434 =
                let uu____435 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____435  in
              (FStar_Errors.Warning_NotEmbedded, uu____434)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____429
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
    let uu___51_456 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___51_456.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___51_456.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____478 ->
        let uu____479 =
          if w
          then
            let uu____480 =
              let uu____485 =
                let uu____486 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____486  in
              (FStar_Errors.Warning_NotEmbedded, uu____485)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____480
          else ()  in
        FStar_Pervasives_Native.None
     in
  mk_emb em un FStar_Syntax_Syntax.t_bool 
let (e_char : FStar_Char.char embedding) =
  let em rng c =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___52_505 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___52_505.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___52_505.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____528 ->
        let uu____529 =
          if w
          then
            let uu____530 =
              let uu____535 =
                let uu____536 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____536  in
              (FStar_Errors.Warning_NotEmbedded, uu____535)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____530
          else ()  in
        FStar_Pervasives_Native.None
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let em rng i =
    let t =
      let uu____554 = FStar_BigInt.string_of_big_int i  in
      FStar_Syntax_Util.exp_int uu____554  in
    let uu___53_555 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___53_555.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___53_555.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____575))
        ->
        let uu____588 = FStar_BigInt.big_int_of_string s  in
        FStar_Pervasives_Native.Some uu____588
    | uu____589 ->
        let uu____590 =
          if w
          then
            let uu____591 =
              let uu____596 =
                let uu____597 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded int: %s" uu____597  in
              (FStar_Errors.Warning_NotEmbedded, uu____596)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____591
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
        (s,uu____631)) -> FStar_Pervasives_Native.Some s
    | uu____632 ->
        let uu____633 =
          if w
          then
            let uu____634 =
              let uu____639 =
                let uu____640 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____640  in
              (FStar_Errors.Warning_NotEmbedded, uu____639)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____634
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
          let uu____675 =
            let uu____680 =
              let uu____681 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____681
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____682 =
              let uu____683 =
                let uu____684 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____684  in
              [uu____683]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____680 uu____682  in
          uu____675 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____688 =
            let uu____693 =
              let uu____694 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____694
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____695 =
              let uu____696 =
                let uu____697 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____697  in
              let uu____698 =
                let uu____701 =
                  let uu____702 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____702  in
                [uu____701]  in
              uu____696 :: uu____698  in
            FStar_Syntax_Syntax.mk_Tm_app uu____693 uu____695  in
          uu____688 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____725 = FStar_Syntax_Util.head_and_args t  in
      match uu____725 with
      | (hd1,args) ->
          let uu____766 =
            let uu____779 =
              let uu____780 = FStar_Syntax_Util.un_uinst hd1  in
              uu____780.FStar_Syntax_Syntax.n  in
            (uu____779, args)  in
          (match uu____766 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____796) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____816::(a,uu____818)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____855 = unembed ea a  in
               FStar_Util.bind_opt uu____855
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____864 ->
               let uu____877 =
                 if w
                 then
                   let uu____878 =
                     let uu____883 =
                       let uu____884 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____884
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____883)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____878
                 else ()  in
               FStar_Pervasives_Native.None)
       in
    let uu____888 =
      let uu____889 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____889  in
    mk_emb em un uu____888
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____945 =
          let uu____950 =
            let uu____951 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____951
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____952 =
            let uu____953 =
              let uu____954 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____954  in
            let uu____955 =
              let uu____958 =
                let uu____959 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____959  in
              let uu____960 =
                let uu____963 =
                  let uu____964 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____964  in
                let uu____965 =
                  let uu____968 =
                    let uu____969 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____969  in
                  [uu____968]  in
                uu____963 :: uu____965  in
              uu____958 :: uu____960  in
            uu____953 :: uu____955  in
          FStar_Syntax_Syntax.mk_Tm_app uu____950 uu____952  in
        uu____945 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____996 = FStar_Syntax_Util.head_and_args t  in
        match uu____996 with
        | (hd1,args) ->
            let uu____1039 =
              let uu____1052 =
                let uu____1053 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1053.FStar_Syntax_Syntax.n  in
              (uu____1052, args)  in
            (match uu____1039 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1071::uu____1072::(a,uu____1074)::(b,uu____1076)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1135 = unembed ea a  in
                 FStar_Util.bind_opt uu____1135
                   (fun a1  ->
                      let uu____1145 = unembed eb b  in
                      FStar_Util.bind_opt uu____1145
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1158 ->
                 let uu____1171 =
                   if w
                   then
                     let uu____1172 =
                       let uu____1177 =
                         let uu____1178 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1178
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1177)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1172
                   else ()  in
                 FStar_Pervasives_Native.None)
         in
      let uu____1184 =
        let uu____1185 = type_of ea  in
        let uu____1186 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1185 uu____1186  in
      mk_emb em un uu____1184
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1225 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1225
         in
      let nil =
        let uu____1229 =
          let uu____1234 =
            let uu____1235 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1235
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1234 [t]  in
        uu____1229 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1239 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1239
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1247 =
               let uu____1252 =
                 let uu____1253 =
                   let uu____1256 =
                     let uu____1257 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1257  in
                   let uu____1258 =
                     let uu____1261 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1261]  in
                   uu____1256 :: uu____1258  in
                 t :: uu____1253  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1252  in
             uu____1247 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1284 = FStar_Syntax_Util.head_and_args t  in
      match uu____1284 with
      | (hd1,args) ->
          let uu____1325 =
            let uu____1338 =
              let uu____1339 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1339.FStar_Syntax_Syntax.n  in
            (uu____1338, args)  in
          (match uu____1325 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1355) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,_t::(hd2,uu____1377)::(tl1,uu____1379)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1426 = unembed ea hd2  in
               FStar_Util.bind_opt uu____1426
                 (fun hd3  ->
                    let uu____1434 = un w tl1  in
                    FStar_Util.bind_opt uu____1434
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1449 ->
               let uu____1462 =
                 if w
                 then
                   let uu____1463 =
                     let uu____1468 =
                       let uu____1469 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1469
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1468)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1463
                 else ()  in
               FStar_Pervasives_Native.None)
       in
    let uu____1473 =
      let uu____1474 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1474  in
    mk_emb em un uu____1473
  
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
    match projectee with | Simpl  -> true | uu____1502 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1508 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1514 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1520 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1526 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1532 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1538 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1547 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1569 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1589 -> false
  
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
        let uu____1613 =
          let uu____1618 =
            let uu____1619 =
              let uu____1620 =
                let uu____1621 = e_list e_string  in embed uu____1621 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1620  in
            [uu____1619]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1618  in
        uu____1613 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____1633 =
          let uu____1638 =
            let uu____1639 =
              let uu____1640 =
                let uu____1641 = e_list e_string  in embed uu____1641 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1640  in
            [uu____1639]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____1638  in
        uu____1633 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____1651 =
          let uu____1656 =
            let uu____1657 = FStar_Syntax_Syntax.as_arg a  in [uu____1657]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1656  in
        uu____1651 FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____1676 = FStar_Syntax_Util.head_and_args t  in
    match uu____1676 with
    | (hd1,args) ->
        let uu____1715 =
          let uu____1728 =
            let uu____1729 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1729.FStar_Syntax_Syntax.n  in
          (uu____1728, args)  in
        (match uu____1715 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1849)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____1874 =
               let uu____1879 = e_list e_string  in unembed uu____1879 l  in
             FStar_Util.bind_opt uu____1874
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1896)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____1921 =
               let uu____1926 = e_list e_string  in unembed uu____1926 l  in
             FStar_Util.bind_opt uu____1921
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1942::(a,uu____1944)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____1981 ->
             let uu____1994 =
               if w
               then
                 let uu____1995 =
                   let uu____2000 =
                     let uu____2001 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____2001
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2000)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1995
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
    | uu____2035 ->
        let uu____2036 =
          if w
          then
            let uu____2037 =
              let uu____2042 =
                let uu____2043 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____2043  in
              (FStar_Errors.Warning_NotEmbedded, uu____2042)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2037
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
          | (x,uu____2113)::[] ->
              let uu____2130 = ua x  in
              FStar_Util.bind_opt uu____2130
                (fun a  ->
                   let uu____2136 =
                     let uu____2137 =
                       let uu____2138 =
                         let uu____2139 = ua x  in FStar_Util.must uu____2139
                          in
                       f uu____2138  in
                     eb1 FStar_Range.dummyRange uu____2137  in
                   FStar_Pervasives_Native.Some uu____2136)
          | uu____2142 -> FStar_Pervasives_Native.None
  
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
            | (x,uu____2237)::(y,uu____2239)::[] ->
                let uu____2266 = ua x  in
                FStar_Util.bind_opt uu____2266
                  (fun a  ->
                     let uu____2272 = ub y  in
                     FStar_Util.bind_opt uu____2272
                       (fun b  ->
                          let uu____2278 =
                            let uu____2279 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2279  in
                          FStar_Pervasives_Native.Some uu____2278))
            | uu____2280 -> FStar_Pervasives_Native.None
  
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
              | (x,uu____2401)::(y,uu____2403)::(z,uu____2405)::[] ->
                  let uu____2442 = ua x  in
                  FStar_Util.bind_opt uu____2442
                    (fun a  ->
                       let uu____2448 = ub y  in
                       FStar_Util.bind_opt uu____2448
                         (fun b  ->
                            let uu____2454 = uc z  in
                            FStar_Util.bind_opt uu____2454
                              (fun c  ->
                                 let uu____2460 =
                                   let uu____2461 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____2461  in
                                 FStar_Pervasives_Native.Some uu____2460)))
              | uu____2462 -> FStar_Pervasives_Native.None
  