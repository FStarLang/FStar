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
let (e_unit : Prims.unit embedding) =
  let em rng u =
    let uu___50_321 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___50_321.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___50_321.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____338 ->
        (if w
         then
           (let uu____340 =
              let uu____345 =
                let uu____346 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____346  in
              (FStar_Errors.Warning_NotEmbedded, uu____345)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____340)
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
    let uu___51_363 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___51_363.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___51_363.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____381 ->
        (if w
         then
           (let uu____383 =
              let uu____388 =
                let uu____389 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____389  in
              (FStar_Errors.Warning_NotEmbedded, uu____388)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____383)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_bool 
let (e_char : FStar_Char.char embedding) =
  let em rng c =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___52_404 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___52_404.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___52_404.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____423 ->
        (if w
         then
           (let uu____425 =
              let uu____430 =
                let uu____431 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____431  in
              (FStar_Errors.Warning_NotEmbedded, uu____430)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____425)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let em rng i =
    let t =
      let uu____445 = FStar_BigInt.string_of_big_int i  in
      FStar_Syntax_Util.exp_int uu____445  in
    let uu___53_446 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___53_446.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___53_446.FStar_Syntax_Syntax.vars)
    }  in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____462))
        ->
        let uu____475 = FStar_BigInt.big_int_of_string s  in
        FStar_Pervasives_Native.Some uu____475
    | uu____476 ->
        (if w
         then
           (let uu____478 =
              let uu____483 =
                let uu____484 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded int: %s" uu____484  in
              (FStar_Errors.Warning_NotEmbedded, uu____483)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____478)
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
        (s,uu____510)) -> FStar_Pervasives_Native.Some s
    | uu____511 ->
        (if w
         then
           (let uu____513 =
              let uu____518 =
                let uu____519 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____519  in
              (FStar_Errors.Warning_NotEmbedded, uu____518)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____513)
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
          let uu____547 =
            let uu____548 =
              let uu____549 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____549
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____550 =
              let uu____551 =
                let uu____552 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____552  in
              [uu____551]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____548 uu____550  in
          uu____547 FStar_Pervasives_Native.None rng
      | FStar_Pervasives_Native.Some a ->
          let uu____556 =
            let uu____557 =
              let uu____558 =
                FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid
                 in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____558
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____559 =
              let uu____560 =
                let uu____561 = type_of ea  in
                FStar_Syntax_Syntax.iarg uu____561  in
              let uu____562 =
                let uu____565 =
                  let uu____566 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____566  in
                [uu____565]  in
              uu____560 :: uu____562  in
            FStar_Syntax_Syntax.mk_Tm_app uu____557 uu____559  in
          uu____556 FStar_Pervasives_Native.None rng
       in
    let un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____585 = FStar_Syntax_Util.head_and_args t  in
      match uu____585 with
      | (hd1,args) ->
          let uu____626 =
            let uu____639 =
              let uu____640 = FStar_Syntax_Util.un_uinst hd1  in
              uu____640.FStar_Syntax_Syntax.n  in
            (uu____639, args)  in
          (match uu____626 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____656) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____676::(a,uu____678)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____715 = unembed ea a  in
               FStar_Util.bind_opt uu____715
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____724 ->
               (if w
                then
                  (let uu____738 =
                     let uu____743 =
                       let uu____744 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____744
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____743)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____738)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____748 =
      let uu____749 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____749  in
    mk_emb em un uu____748
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em rng x =
        let uu____795 =
          let uu____796 =
            let uu____797 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2
               in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____797
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
             in
          let uu____798 =
            let uu____799 =
              let uu____800 = type_of ea  in
              FStar_Syntax_Syntax.iarg uu____800  in
            let uu____801 =
              let uu____804 =
                let uu____805 = type_of eb  in
                FStar_Syntax_Syntax.iarg uu____805  in
              let uu____806 =
                let uu____809 =
                  let uu____810 =
                    embed ea rng (FStar_Pervasives_Native.fst x)  in
                  FStar_Syntax_Syntax.as_arg uu____810  in
                let uu____811 =
                  let uu____814 =
                    let uu____815 =
                      embed eb rng (FStar_Pervasives_Native.snd x)  in
                    FStar_Syntax_Syntax.as_arg uu____815  in
                  [uu____814]  in
                uu____809 :: uu____811  in
              uu____804 :: uu____806  in
            uu____799 :: uu____801  in
          FStar_Syntax_Syntax.mk_Tm_app uu____796 uu____798  in
        uu____795 FStar_Pervasives_Native.None rng  in
      let un w t0 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____838 = FStar_Syntax_Util.head_and_args t  in
        match uu____838 with
        | (hd1,args) ->
            let uu____881 =
              let uu____894 =
                let uu____895 = FStar_Syntax_Util.un_uinst hd1  in
                uu____895.FStar_Syntax_Syntax.n  in
              (uu____894, args)  in
            (match uu____881 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____913::uu____914::(a,uu____916)::(b,uu____918)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____977 = unembed ea a  in
                 FStar_Util.bind_opt uu____977
                   (fun a1  ->
                      let uu____987 = unembed eb b  in
                      FStar_Util.bind_opt uu____987
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____1000 ->
                 (if w
                  then
                    (let uu____1014 =
                       let uu____1019 =
                         let uu____1020 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____1020
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1019)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1014)
                  else ();
                  FStar_Pervasives_Native.None))
         in
      let uu____1026 =
        let uu____1027 = type_of ea  in
        let uu____1028 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____1027 uu____1028  in
      mk_emb em un uu____1026
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em rng l =
      let t =
        let uu____1060 = type_of ea  in FStar_Syntax_Syntax.iarg uu____1060
         in
      let nil =
        let uu____1064 =
          let uu____1065 =
            let uu____1066 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1066
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____1065 [t]  in
        uu____1064 FStar_Pervasives_Native.None rng  in
      let cons1 =
        let uu____1070 =
          FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1070
          [FStar_Syntax_Syntax.U_zero]
         in
      FStar_List.fold_right
        (fun hd1  ->
           fun tail1  ->
             let uu____1078 =
               let uu____1079 =
                 let uu____1080 =
                   let uu____1083 =
                     let uu____1084 = embed ea rng hd1  in
                     FStar_Syntax_Syntax.as_arg uu____1084  in
                   let uu____1085 =
                     let uu____1088 = FStar_Syntax_Syntax.as_arg tail1  in
                     [uu____1088]  in
                   uu____1083 :: uu____1085  in
                 t :: uu____1080  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1079  in
             uu____1078 FStar_Pervasives_Native.None rng) l nil
       in
    let rec un w t0 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____1107 = FStar_Syntax_Util.head_and_args t  in
      match uu____1107 with
      | (hd1,args) ->
          let uu____1148 =
            let uu____1161 =
              let uu____1162 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1162.FStar_Syntax_Syntax.n  in
            (uu____1161, args)  in
          (match uu____1148 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1178) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,_t::(hd2,uu____1200)::(tl1,uu____1202)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____1249 = unembed ea hd2  in
               FStar_Util.bind_opt uu____1249
                 (fun hd3  ->
                    let uu____1257 = un w tl1  in
                    FStar_Util.bind_opt uu____1257
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____1272 ->
               (if w
                then
                  (let uu____1286 =
                     let uu____1291 =
                       let uu____1292 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1292
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1291)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1286)
                else ();
                FStar_Pervasives_Native.None))
       in
    let uu____1296 =
      let uu____1297 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____1297  in
    mk_emb em un uu____1296
  
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
    match projectee with | Simpl  -> true | uu____1323 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1327 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1331 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1335 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1339 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1343 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1347 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1354 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____1374 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____1392 -> false
  
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
        let uu____1412 =
          let uu____1413 =
            let uu____1414 =
              let uu____1415 =
                let uu____1416 = e_list e_string  in embed uu____1416 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1415  in
            [uu____1414]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1413  in
        uu____1412 FStar_Pervasives_Native.None rng
    | UnfoldFully l ->
        let uu____1428 =
          let uu____1429 =
            let uu____1430 =
              let uu____1431 =
                let uu____1432 = e_list e_string  in embed uu____1432 rng l
                 in
              FStar_Syntax_Syntax.as_arg uu____1431  in
            [uu____1430]  in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____1429  in
        uu____1428 FStar_Pervasives_Native.None rng
    | UnfoldAttr a ->
        let uu____1442 =
          let uu____1443 =
            let uu____1444 = FStar_Syntax_Syntax.as_arg a  in [uu____1444]
             in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1443  in
        uu____1442 FStar_Pervasives_Native.None rng
     in
  let un w t0 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    let uu____1459 = FStar_Syntax_Util.head_and_args t  in
    match uu____1459 with
    | (hd1,args) ->
        let uu____1498 =
          let uu____1511 =
            let uu____1512 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1512.FStar_Syntax_Syntax.n  in
          (uu____1511, args)  in
        (match uu____1498 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1632)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____1657 =
               let uu____1662 = e_list e_string  in unembed uu____1662 l  in
             FStar_Util.bind_opt uu____1657
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                    (UnfoldOnly ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1679)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldfully
             ->
             let uu____1704 =
               let uu____1709 = e_list e_string  in unembed uu____1709 l  in
             FStar_Util.bind_opt uu____1704
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (UnfoldFully ss))
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1725::(a,uu____1727)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldattr
             -> FStar_Pervasives_Native.Some (UnfoldAttr a)
         | uu____1764 ->
             (if w
              then
                (let uu____1778 =
                   let uu____1783 =
                     let uu____1784 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____1784
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1783)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1778)
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
    | uu____1810 ->
        (if w
         then
           (let uu____1812 =
              let uu____1817 =
                let uu____1818 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____1818  in
              (FStar_Errors.Warning_NotEmbedded, uu____1817)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1812)
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
          | (x,uu____1872)::[] ->
              let uu____1889 = ua x  in
              FStar_Util.bind_opt uu____1889
                (fun a  ->
                   let uu____1895 =
                     let uu____1896 =
                       let uu____1897 =
                         let uu____1898 = ua x  in FStar_Util.must uu____1898
                          in
                       f uu____1897  in
                     eb1 FStar_Range.dummyRange uu____1896  in
                   FStar_Pervasives_Native.Some uu____1895)
          | uu____1901 -> FStar_Pervasives_Native.None
  
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
            | (x,uu____1975)::(y,uu____1977)::[] ->
                let uu____2004 = ua x  in
                FStar_Util.bind_opt uu____2004
                  (fun a  ->
                     let uu____2010 = ub y  in
                     FStar_Util.bind_opt uu____2010
                       (fun b  ->
                          let uu____2016 =
                            let uu____2017 = f a b  in
                            ec1 FStar_Range.dummyRange uu____2017  in
                          FStar_Pervasives_Native.Some uu____2016))
            | uu____2018 -> FStar_Pervasives_Native.None
  
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
              | (x,uu____2113)::(y,uu____2115)::(z,uu____2117)::[] ->
                  let uu____2154 = ua x  in
                  FStar_Util.bind_opt uu____2154
                    (fun a  ->
                       let uu____2160 = ub y  in
                       FStar_Util.bind_opt uu____2160
                         (fun b  ->
                            let uu____2166 = uc z  in
                            FStar_Util.bind_opt uu____2166
                              (fun c  ->
                                 let uu____2172 =
                                   let uu____2173 = f a b c  in
                                   ed1 FStar_Range.dummyRange uu____2173  in
                                 FStar_Pervasives_Native.Some uu____2172)))
              | uu____2174 -> FStar_Pervasives_Native.None
  