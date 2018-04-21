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
    let uu___51_462 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___51_462.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___51_462.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____482 ->
        (if w
         then
           (let uu____484 =
              let uu____489 =
                let uu____490 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____490  in
              (FStar_Errors.Warning_NotEmbedded, uu____489)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____484)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_bool 
let (e_char : FStar_Char.char embedding) =
  let em rng c =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___52_509 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___52_509.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___52_509.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____532 ->
        (if w
         then
           (let uu____534 =
              let uu____539 =
                let uu____540 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____540  in
              (FStar_Errors.Warning_NotEmbedded, uu____539)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____534)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let em rng i =
    let t =
      let uu____558 = FStar_BigInt.string_of_big_int i  in
      FStar_Syntax_Util.exp_int uu____558  in
    let uu___53_559 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___53_559.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___53_559.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____579))
        ->
        let uu____592 = FStar_BigInt.big_int_of_string s  in
        FStar_Pervasives_Native.Some uu____592
    | uu____593 ->
        (if w
         then
           (let uu____595 =
              let uu____600 =
                let uu____601 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded int: %s" uu____601  in
              (FStar_Errors.Warning_NotEmbedded, uu____600)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____595)
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
        (s,uu____635)) -> FStar_Pervasives_Native.Some s
    | uu____636 ->
        (if w
         then
           (let uu____638 =
              let uu____643 =
                let uu____644 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____644  in
              (FStar_Errors.Warning_NotEmbedded, uu____643)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____638)
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
          let uu____679 =
            let uu____684 =
              let uu____685 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____685
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____686 =
              let uu____687 =
                let uu____688 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____688  in
              [uu____687]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____684 uu____686  in
          uu____679 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____692 =
            let uu____697 =
              let uu____698 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____698
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____699 =
              let uu____700 =
                let uu____701 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____701  in
              let uu____702 =
                let uu____705 =
                  let uu____706 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____706  in
                [uu____705]  in
              uu____700 :: uu____702  in
            FStar_Syntax_Syntax.mk_Tm_app uu____697 uu____699  in
          uu____692 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____729 = FStar_Syntax_Util.head_and_args t  in
      match uu____729 with
      | (hd1,args) ->
          let uu____770 =
            let uu____783 =
              let uu____784 = FStar_Syntax_Util.un_uinst hd1  in
              uu____784.FStar_Syntax_Syntax.n  in
            (uu____783, args)  in
          (match uu____770 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____800) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____820::(a,uu____822)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____859 = unembed ea a  in
               FStar_Util.bind_opt uu____859
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____868 ->
               (if w
                then
                  (let uu____882 =
                     let uu____887 =
                       let uu____888 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____888
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____887)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____882)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____892 =
      let uu____893 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____893  in
    mk_emb em un uu____892
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____949 =
          let uu____954 =
            let uu____955 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____955
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____956 =
            let uu____957 =
              let uu____958 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____958  in
            let uu____959 =
              let uu____962 =
                let uu____963 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____963  in
              let uu____964 =
                let uu____967 =
                  let uu____968 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____968  in
                let uu____969 =
                  let uu____972 =
                    let uu____973 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____973  in
                  [uu____972]  in
                uu____967 :: uu____969  in
              uu____962 :: uu____964  in
            uu____957 :: uu____959  in
          FStar_Syntax_Syntax.mk_Tm_app uu____954 uu____956  in
        uu____949 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1000 = FStar_Syntax_Util.head_and_args t  in
        match uu____1000 with
        | (hd1,args) ->
            let uu____1043 =
              let uu____1056 =
                let uu____1057 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1057.FStar_Syntax_Syntax.n  in
              (uu____1056, args)  in
            (match uu____1043 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1075::uu____1076::(a,uu____1078)::(b,uu____1080)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____1139 = unembed ea a  in
                 FStar_Util.bind_opt uu____1139
                   (fun a1  ->
                      let uu____1149 = unembed eb b  in
                      FStar_Util.bind_opt uu____1149
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1162 ->
                 (if w
                  then
                    (let uu____1176 =
                       let uu____1181 =
                         let uu____1182 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1182
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1181)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1176)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1188 =
        let uu____1189 = type_of ea  in
        let uu____1190 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1189 uu____1190  in
      mk_emb em un uu____1188
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1229 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1229
         in
      let nil =
        let uu____1233 =
          let uu____1238 =
            let uu____1239 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1239
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1238 [t]  in
        uu____1233 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1243 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1243
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1251 =
               let uu____1256 =
                 let uu____1257 =
                   let uu____1260 =
                     let uu____1261 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1261  in
                   let uu____1262 =
                     let uu____1265 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1265]  in
                   uu____1260 :: uu____1262  in
                 t :: uu____1257  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1256  in
             uu____1251 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1288 = FStar_Syntax_Util.head_and_args t  in
      match uu____1288 with
      | (hd1,args) ->
          let uu____1329 =
            let uu____1342 =
              let uu____1343 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1343.FStar_Syntax_Syntax.n  in
            (uu____1342, args)  in
          (match uu____1329 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1359) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,_t::(hd2,uu____1381)::(tl1,uu____1383)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1430 = unembed ea hd2  in
               FStar_Util.bind_opt uu____1430
                 (fun hd3  ->
                    let uu____1438 = un w tl1  in
                    FStar_Util.bind_opt uu____1438
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1453 ->
               (if w
                then
                  (let uu____1467 =
                     let uu____1472 =
                       let uu____1473 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1473
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1472)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1467)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1477 =
      let uu____1478 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1478  in
    mk_emb em un uu____1477
  
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
    match projectee with | Simpl  -> true | uu____1509 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1515 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1521 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1527 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1533 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1539 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1545 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1554 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1576 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1596 -> false
  
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
        let uu____1620 =
          let uu____1625 =
            let uu____1626 =
              let uu____1627 =
                let uu____1628 = e_list e_string  in embed uu____1628 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1627  in
            [uu____1626]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1625  in
        uu____1620 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____1640 =
          let uu____1645 =
            let uu____1646 =
              let uu____1647 =
                let uu____1648 = e_list e_string  in embed uu____1648 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1647  in
            [uu____1646]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____1645  in
        uu____1640 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____1658 =
          let uu____1663 =
            let uu____1664 = FStar_Syntax_Syntax.as_arg a  in [uu____1664]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1663  in
        uu____1658 FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____1683 = FStar_Syntax_Util.head_and_args t  in
    match uu____1683 with
    | (hd1,args) ->
        let uu____1722 =
          let uu____1735 =
            let uu____1736 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1736.FStar_Syntax_Syntax.n  in
          (uu____1735, args)  in
        (match uu____1722 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1856)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____1881 =
               let uu____1886 = e_list e_string  in unembed uu____1886 l  in
             FStar_Util.bind_opt uu____1881
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1903)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____1928 =
               let uu____1933 = e_list e_string  in unembed uu____1933 l  in
             FStar_Util.bind_opt uu____1928
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1949::(a,uu____1951)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____1988 ->
             (if w
              then
                (let uu____2002 =
                   let uu____2007 =
                     let uu____2008 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____2008
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2007)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2002)
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
    | uu____2042 ->
        (if w
         then
           (let uu____2044 =
              let uu____2049 =
                let uu____2050 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____2050  in
              (FStar_Errors.Warning_NotEmbedded, uu____2049)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2044)
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
          | (x,uu____2120)::[] ->
              let uu____2137 = ua x  in
              FStar_Util.bind_opt uu____2137
                (fun a  ->
                   let uu____2143 =
                     let uu____2144 =
                       let uu____2145 =
                         let uu____2146 = ua x  in FStar_Util.must uu____2146
                          in
                       f uu____2145  in
                     eb1 FStar_Range.dummyRange uu____2144  in
                   FStar_Pervasives_Native.Some uu____2143)
          | uu____2149 -> FStar_Pervasives_Native.None
  
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
            | (x,uu____2244)::(y,uu____2246)::[] ->
                let uu____2273 = ua x  in
                FStar_Util.bind_opt uu____2273
                  (fun a  ->
                     let uu____2279 = ub y  in
                     FStar_Util.bind_opt uu____2279
                       (fun b  ->
                          let uu____2285 =
                            let uu____2286 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2286  in
                          FStar_Pervasives_Native.Some uu____2285))
            | uu____2287 -> FStar_Pervasives_Native.None
  
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
              | (x,uu____2408)::(y,uu____2410)::(z,uu____2412)::[] ->
                  let uu____2449 = ua x  in
                  FStar_Util.bind_opt uu____2449
                    (fun a  ->
                       let uu____2455 = ub y  in
                       FStar_Util.bind_opt uu____2455
                         (fun b  ->
                            let uu____2461 = uc z  in
                            FStar_Util.bind_opt uu____2461
                              (fun c  ->
                                 let uu____2467 =
                                   let uu____2468 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____2468  in
                                 FStar_Pervasives_Native.Some uu____2467)))
              | uu____2469 -> FStar_Pervasives_Native.None
  