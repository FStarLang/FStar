open Prims
type 'a embedder = FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
[@@deriving show]
type 'a unembedder =
  FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option[@@deriving
                                                                 show]
let (embed_any :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun r  -> fun t  -> t 
let (unembed_any :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun t  -> FStar_Pervasives_Native.Some t 
let (embed_unit :
  FStar_Range.range -> Prims.unit -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun u  ->
      let uu___48_46 = FStar_Syntax_Util.exp_unit  in
      {
        FStar_Syntax_Syntax.n = (uu___48_46.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___48_46.FStar_Syntax_Syntax.vars)
      }
  
let (__unembed_unit :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option)
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unascribe t0  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
          FStar_Pervasives_Native.Some ()
      | uu____62 ->
          (if w
           then
             (let uu____64 =
                let uu____69 =
                  let uu____70 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded unit: %s" uu____70  in
                (FStar_Errors.Warning_NotEmbedded, uu____69)  in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____64)
           else ();
           FStar_Pervasives_Native.None)
  
let (unembed_unit :
  FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option) =
  fun t  -> __unembed_unit true t 
let (unembed_unit_safe :
  FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option) =
  fun t  -> __unembed_unit false t 
let (embed_bool :
  FStar_Range.range -> Prims.bool -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun b  ->
      let t =
        if b
        then FStar_Syntax_Util.exp_true_bool
        else FStar_Syntax_Util.exp_false_bool  in
      let uu___49_101 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___49_101.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___49_101.FStar_Syntax_Syntax.vars)
      }
  
let (__unembed_bool :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option)
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
          FStar_Pervasives_Native.Some b
      | uu____118 ->
          (if w
           then
             (let uu____120 =
                let uu____125 =
                  let uu____126 = FStar_Syntax_Print.term_to_string t0  in
                  FStar_Util.format1 "Not an embedded bool: %s" uu____126  in
                (FStar_Errors.Warning_NotEmbedded, uu____125)  in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____120)
           else ();
           FStar_Pervasives_Native.None)
  
let (unembed_bool :
  FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option) =
  fun t  -> __unembed_bool true t 
let (unembed_bool_safe :
  FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option) =
  fun t  -> __unembed_bool false t 
let (embed_char :
  FStar_Range.range -> FStar_Char.char -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun c  ->
      let t = FStar_Syntax_Util.exp_char c  in
      let uu___50_154 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___50_154.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___50_154.FStar_Syntax_Syntax.vars)
      }
  
let (__unembed_char :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Char.char FStar_Pervasives_Native.option)
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
          FStar_Pervasives_Native.Some c
      | uu____172 ->
          (if w
           then
             (let uu____174 =
                let uu____179 =
                  let uu____180 = FStar_Syntax_Print.term_to_string t0  in
                  FStar_Util.format1 "Not an embedded char: %s" uu____180  in
                (FStar_Errors.Warning_NotEmbedded, uu____179)  in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____174)
           else ();
           FStar_Pervasives_Native.None)
  
let (unembed_char :
  FStar_Syntax_Syntax.term -> FStar_Char.char FStar_Pervasives_Native.option)
  = fun t  -> __unembed_char true t 
let (unembed_char_safe :
  FStar_Syntax_Syntax.term -> FStar_Char.char FStar_Pervasives_Native.option)
  = fun t  -> __unembed_char false t 
let (embed_int :
  FStar_Range.range -> FStar_BigInt.t -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun i  ->
      let t =
        let uu____209 = FStar_BigInt.string_of_big_int i  in
        FStar_Syntax_Util.exp_int uu____209  in
      let uu___51_210 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___51_210.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___51_210.FStar_Syntax_Syntax.vars)
      }
  
let (__unembed_int :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option)
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____225))
          ->
          let uu____238 = FStar_BigInt.big_int_of_string s  in
          FStar_Pervasives_Native.Some uu____238
      | uu____239 ->
          (if w
           then
             (let uu____241 =
                let uu____246 =
                  let uu____247 = FStar_Syntax_Print.term_to_string t0  in
                  FStar_Util.format1 "Not an embedded int: %s" uu____247  in
                (FStar_Errors.Warning_NotEmbedded, uu____246)  in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____241)
           else ();
           FStar_Pervasives_Native.None)
  
let (unembed_int :
  FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option)
  = fun t  -> __unembed_int true t 
let (unembed_int_safe :
  FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option)
  = fun t  -> __unembed_int false t 
let (embed_string :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun s  ->
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
        FStar_Pervasives_Native.None rng
  
let (__unembed_string :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
          (s,uu____286)) -> FStar_Pervasives_Native.Some s
      | uu____287 ->
          (if w
           then
             (let uu____289 =
                let uu____294 =
                  let uu____295 = FStar_Syntax_Print.term_to_string t0  in
                  FStar_Util.format1 "Not an embedded string: %s" uu____295
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____294)  in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____289)
           else ();
           FStar_Pervasives_Native.None)
  
let (unembed_string :
  FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option) =
  fun t  -> __unembed_string true t 
let (unembed_string_safe :
  FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option) =
  fun t  -> __unembed_string false t 
let embed_pair :
  'a 'b .
    'a embedder ->
      FStar_Syntax_Syntax.typ ->
        'b embedder ->
          FStar_Syntax_Syntax.typ ->
            ('a,'b) FStar_Pervasives_Native.tuple2 embedder
  =
  fun embed_a  ->
    fun t_a  ->
      fun embed_b  ->
        fun t_b  ->
          fun rng  ->
            fun x  ->
              let uu____378 =
                let uu____379 =
                  let uu____380 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.lid_Mktuple2
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____380
                    [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   in
                let uu____381 =
                  let uu____382 = FStar_Syntax_Syntax.iarg t_a  in
                  let uu____383 =
                    let uu____386 = FStar_Syntax_Syntax.iarg t_b  in
                    let uu____387 =
                      let uu____390 =
                        let uu____391 =
                          embed_a rng (FStar_Pervasives_Native.fst x)  in
                        FStar_Syntax_Syntax.as_arg uu____391  in
                      let uu____395 =
                        let uu____398 =
                          let uu____399 =
                            embed_b rng (FStar_Pervasives_Native.snd x)  in
                          FStar_Syntax_Syntax.as_arg uu____399  in
                        [uu____398]  in
                      uu____390 :: uu____395  in
                    uu____386 :: uu____387  in
                  uu____382 :: uu____383  in
                FStar_Syntax_Syntax.mk_Tm_app uu____379 uu____381  in
              uu____378 FStar_Pervasives_Native.None rng
  
let embed_tuple2 :
  'a 'b .
    'a embedder ->
      FStar_Syntax_Syntax.typ ->
        'b embedder ->
          FStar_Syntax_Syntax.typ ->
            ('a,'b) FStar_Pervasives_Native.tuple2 embedder
  =
  fun ea  ->
    fun ta  ->
      fun eb  ->
        fun tb  ->
          fun rng  ->
            fun x  ->
              let uu____472 = embed_pair ea ta eb tb  in uu____472 rng x
  
let __unembed_pair :
  'a 'b .
    Prims.bool ->
      'a unembedder ->
        'b unembedder ->
          FStar_Syntax_Syntax.term ->
            ('a,'b) FStar_Pervasives_Native.tuple2
              FStar_Pervasives_Native.option
  =
  fun w  ->
    fun unembed_a  ->
      fun unembed_b  ->
        fun t0  ->
          let t = FStar_Syntax_Util.unmeta_safe t0  in
          let uu____541 = FStar_Syntax_Util.head_and_args t  in
          match uu____541 with
          | (hd1,args) ->
              let uu____584 =
                let uu____597 =
                  let uu____598 = FStar_Syntax_Util.un_uinst hd1  in
                  uu____598.FStar_Syntax_Syntax.n  in
                (uu____597, args)  in
              (match uu____584 with
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,uu____616::uu____617::(a,uu____619)::(b,uu____621)::[])
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.lid_Mktuple2
                   ->
                   let uu____680 = unembed_a a  in
                   FStar_Util.bind_opt uu____680
                     (fun a1  ->
                        let uu____692 = unembed_b b  in
                        FStar_Util.bind_opt uu____692
                          (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
               | uu____707 ->
                   (if w
                    then
                      (let uu____721 =
                         let uu____726 =
                           let uu____727 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1 "Not an embedded pair: %s"
                             uu____727
                            in
                         (FStar_Errors.Warning_NotEmbedded, uu____726)  in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____721)
                    else ();
                    FStar_Pervasives_Native.None))
  
let unembed_pair :
  'a 'b .
    'a unembedder ->
      'b unembedder -> ('a,'b) FStar_Pervasives_Native.tuple2 unembedder
  = fun ul  -> fun ur  -> fun t  -> __unembed_pair true ul ur t 
let unembed_pair_safe :
  'a 'b .
    'a unembedder ->
      'b unembedder -> ('a,'b) FStar_Pervasives_Native.tuple2 unembedder
  = fun ul  -> fun ur  -> fun t  -> __unembed_pair false ul ur t 
let unembed_tuple2 :
  'a 'b .
    'a unembedder ->
      'b unembedder -> ('a,'b) FStar_Pervasives_Native.tuple2 unembedder
  =
  fun ul  ->
    fun ur  -> fun t  -> let uu____881 = unembed_pair ul ur  in uu____881 t
  
let unembed_tuple2_safe :
  'a 'b .
    'a unembedder ->
      'b unembedder -> ('a,'b) FStar_Pervasives_Native.tuple2 unembedder
  =
  fun ul  ->
    fun ur  ->
      fun t  -> let uu____942 = unembed_pair_safe ul ur  in uu____942 t
  
let embed_option :
  'a .
    'a embedder ->
      FStar_Syntax_Syntax.typ -> 'a FStar_Pervasives_Native.option embedder
  =
  fun embed_a  ->
    fun typ  ->
      fun rng  ->
        fun o  ->
          match o with
          | FStar_Pervasives_Native.None  ->
              let uu____1000 =
                let uu____1001 =
                  let uu____1002 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.none_lid
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1002
                    [FStar_Syntax_Syntax.U_zero]
                   in
                let uu____1003 =
                  let uu____1004 = FStar_Syntax_Syntax.iarg typ  in
                  [uu____1004]  in
                FStar_Syntax_Syntax.mk_Tm_app uu____1001 uu____1003  in
              uu____1000 FStar_Pervasives_Native.None rng
          | FStar_Pervasives_Native.Some a ->
              let uu____1008 =
                let uu____1009 =
                  let uu____1010 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.some_lid
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1010
                    [FStar_Syntax_Syntax.U_zero]
                   in
                let uu____1011 =
                  let uu____1012 = FStar_Syntax_Syntax.iarg typ  in
                  let uu____1013 =
                    let uu____1016 =
                      let uu____1017 = embed_a rng a  in
                      FStar_Syntax_Syntax.as_arg uu____1017  in
                    [uu____1016]  in
                  uu____1012 :: uu____1013  in
                FStar_Syntax_Syntax.mk_Tm_app uu____1009 uu____1011  in
              uu____1008 FStar_Pervasives_Native.None rng
  
let __unembed_option :
  'a .
    Prims.bool ->
      'a unembedder ->
        FStar_Syntax_Syntax.term ->
          'a FStar_Pervasives_Native.option FStar_Pervasives_Native.option
  =
  fun w  ->
    fun unembed_a  ->
      fun t0  ->
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1053 = FStar_Syntax_Util.head_and_args t  in
        match uu____1053 with
        | (hd1,args) ->
            let uu____1094 =
              let uu____1107 =
                let uu____1108 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1108.FStar_Syntax_Syntax.n  in
              (uu____1107, args)  in
            (match uu____1094 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1124) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
                 -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1144::(a,uu____1146)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
                 ->
                 let uu____1183 = unembed_a a  in
                 FStar_Util.bind_opt uu____1183
                   (fun a1  ->
                      FStar_Pervasives_Native.Some
                        (FStar_Pervasives_Native.Some a1))
             | uu____1194 ->
                 (if w
                  then
                    (let uu____1208 =
                       let uu____1213 =
                         let uu____1214 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded option: %s"
                           uu____1214
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1213)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1208)
                  else ();
                  FStar_Pervasives_Native.None))
  
let unembed_option :
  'a . 'a unembedder -> 'a FStar_Pervasives_Native.option unembedder =
  fun ua  -> fun t  -> __unembed_option true ua t 
let unembed_option_safe :
  'a . 'a unembedder -> 'a FStar_Pervasives_Native.option unembedder =
  fun ua  -> fun t  -> __unembed_option false ua t 
let embed_list :
  'a . 'a embedder -> FStar_Syntax_Syntax.typ -> 'a Prims.list embedder =
  fun embed_a  ->
    fun typ  ->
      fun rng  ->
        fun l  ->
          let t = FStar_Syntax_Syntax.iarg typ  in
          let nil =
            let uu____1325 =
              let uu____1326 =
                let uu____1327 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid
                   in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____1327
                  [FStar_Syntax_Syntax.U_zero]
                 in
              FStar_Syntax_Syntax.mk_Tm_app uu____1326 [t]  in
            uu____1325 FStar_Pervasives_Native.None rng  in
          let cons1 =
            let uu____1331 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1331
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_List.fold_right
            (fun hd1  ->
               fun tail1  ->
                 let uu____1339 =
                   let uu____1340 =
                     let uu____1341 =
                       let uu____1344 =
                         let uu____1345 = embed_a rng hd1  in
                         FStar_Syntax_Syntax.as_arg uu____1345  in
                       let uu____1349 =
                         let uu____1352 = FStar_Syntax_Syntax.as_arg tail1
                            in
                         [uu____1352]  in
                       uu____1344 :: uu____1349  in
                     t :: uu____1341  in
                   FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1340  in
                 uu____1339 FStar_Pervasives_Native.None rng) l nil
  
let rec __unembed_list :
  'a .
    Prims.bool ->
      'a unembedder ->
        FStar_Syntax_Syntax.term ->
          'a Prims.list FStar_Pervasives_Native.option
  =
  fun w  ->
    fun unembed_a  ->
      fun t0  ->
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        let uu____1386 = FStar_Syntax_Util.head_and_args t  in
        match uu____1386 with
        | (hd1,args) ->
            let uu____1427 =
              let uu____1440 =
                let uu____1441 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1441.FStar_Syntax_Syntax.n  in
              (uu____1440, args)  in
            (match uu____1427 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1457) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> FStar_Pervasives_Native.Some []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,_t::(hd2,uu____1479)::(tl1,uu____1481)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1528 = unembed_a hd2  in
                 FStar_Util.bind_opt uu____1528
                   (fun hd3  ->
                      let uu____1538 = __unembed_list w unembed_a tl1  in
                      FStar_Util.bind_opt uu____1538
                        (fun tl2  ->
                           FStar_Pervasives_Native.Some (hd3 :: tl2)))
             | uu____1557 ->
                 (if w
                  then
                    (let uu____1571 =
                       let uu____1576 =
                         let uu____1577 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1 "Not an embedded list: %s"
                           uu____1577
                          in
                       (FStar_Errors.Warning_NotEmbedded, uu____1576)  in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1571)
                  else ();
                  FStar_Pervasives_Native.None))
  
let unembed_list : 'a . 'a unembedder -> 'a Prims.list unembedder =
  fun ua  -> fun t  -> __unembed_list true ua t 
let unembed_list_safe : 'a . 'a unembedder -> 'a Prims.list unembedder =
  fun ua  -> fun t  -> __unembed_list false ua t 
let embed_arrow_1 :
  'a 'b .
    'a unembedder ->
      'b embedder ->
        ('a -> 'b) ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ua  ->
    fun eb  ->
      fun f  ->
        fun args  ->
          match args with
          | (x,uu____1695)::[] ->
              let uu____1712 = ua x  in
              FStar_Util.bind_opt uu____1712
                (fun a  ->
                   let uu____1720 =
                     let uu____1721 =
                       let uu____1722 =
                         let uu____1723 = ua x  in FStar_Util.must uu____1723
                          in
                       f uu____1722  in
                     eb FStar_Range.dummyRange uu____1721  in
                   FStar_Pervasives_Native.Some uu____1720)
          | uu____1731 -> FStar_Pervasives_Native.None
  
let embed_arrow_2 :
  'a 'b 'd .
    'a unembedder ->
      'b unembedder ->
        'd embedder ->
          ('a -> 'b -> 'd) ->
            FStar_Syntax_Syntax.args ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ua  ->
    fun ub  ->
      fun ed  ->
        fun f  ->
          fun args  ->
            match args with
            | (x,uu____1804)::(y,uu____1806)::[] ->
                let uu____1833 = ua x  in
                FStar_Util.bind_opt uu____1833
                  (fun a  ->
                     let uu____1841 = ub y  in
                     FStar_Util.bind_opt uu____1841
                       (fun b  ->
                          let uu____1849 =
                            let uu____1850 = f a b  in
                            ed FStar_Range.dummyRange uu____1850  in
                          FStar_Pervasives_Native.Some uu____1849))
            | uu____1854 -> FStar_Pervasives_Native.None
  
let embed_arrow_3 :
  'a 'b 'c 'd .
    'a unembedder ->
      'b unembedder ->
        'c unembedder ->
          'd embedder ->
            ('a -> 'b -> 'c -> 'd) ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ua  ->
    fun ub  ->
      fun uc  ->
        fun ed  ->
          fun f  ->
            fun args  ->
              match args with
              | (x,uu____1947)::(y,uu____1949)::(z,uu____1951)::[] ->
                  let uu____1988 = ua x  in
                  FStar_Util.bind_opt uu____1988
                    (fun a  ->
                       let uu____1996 = ub y  in
                       FStar_Util.bind_opt uu____1996
                         (fun b  ->
                            let uu____2004 = uc z  in
                            FStar_Util.bind_opt uu____2004
                              (fun c  ->
                                 let uu____2012 =
                                   let uu____2013 = f a b c  in
                                   ed FStar_Range.dummyRange uu____2013  in
                                 FStar_Pervasives_Native.Some uu____2012)))
              | uu____2017 -> FStar_Pervasives_Native.None
  
let (embed_string_list :
  FStar_Range.range -> Prims.string Prims.list -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun ss  ->
      let uu____2031 = embed_list embed_string FStar_Syntax_Syntax.t_string
         in
      uu____2031 rng ss
  
let (unembed_string_list :
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option)
  = fun t  -> let uu____2048 = unembed_list unembed_string  in uu____2048 t 
let (unembed_string_list_safe :
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____2064 = unembed_list_safe unembed_string_safe  in uu____2064 t
  
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | Iota 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute [@@deriving show]
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____2084 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____2088 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____2092 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____2096 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____2100 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____2104 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____2108 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____2115 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____2133 -> false
  
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
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldattr 
let (embed_norm_step :
  FStar_Range.range -> norm_step -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun n1  ->
      match n1 with
      | Simpl  -> steps_Simpl
      | Weak  -> steps_Weak
      | HNF  -> steps_HNF
      | Primops  -> steps_Primops
      | Delta  -> steps_Delta
      | Zeta  -> steps_Zeta
      | Iota  -> steps_Iota
      | UnfoldOnly l ->
          let uu____2153 =
            let uu____2154 =
              let uu____2155 =
                let uu____2156 =
                  let uu____2157 =
                    embed_list embed_string FStar_Syntax_Syntax.t_string  in
                  uu____2157 rng l  in
                FStar_Syntax_Syntax.as_arg uu____2156  in
              [uu____2155]  in
            FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____2154  in
          uu____2153 FStar_Pervasives_Native.None rng
      | UnfoldAttr a ->
          let uu____2168 =
            let uu____2169 =
              let uu____2170 = FStar_Syntax_Syntax.as_arg a  in [uu____2170]
               in
            FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____2169  in
          uu____2168 FStar_Pervasives_Native.None rng
  
let (__unembed_norm_step :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option)
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      let uu____2184 = FStar_Syntax_Util.head_and_args t  in
      match uu____2184 with
      | (hd1,args) ->
          let uu____2223 =
            let uu____2236 =
              let uu____2237 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2237.FStar_Syntax_Syntax.n  in
            (uu____2236, args)  in
          (match uu____2223 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_simpl
               -> FStar_Pervasives_Native.Some Simpl
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak
               -> FStar_Pervasives_Native.Some Weak
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf
               -> FStar_Pervasives_Native.Some HNF
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_primops
               -> FStar_Pervasives_Native.Some Primops
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_delta
               -> FStar_Pervasives_Native.Some Delta
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta
               -> FStar_Pervasives_Native.Some Zeta
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota
               -> FStar_Pervasives_Native.Some Iota
           | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____2357)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_unfoldonly
               ->
               let uu____2382 =
                 let uu____2387 = unembed_list unembed_string  in
                 uu____2387 l  in
               FStar_Util.bind_opt uu____2382
                 (fun ss  ->
                    FStar_All.pipe_left
                      (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                      (UnfoldOnly ss))
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2403::(a,uu____2405)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_unfoldattr
               -> FStar_Pervasives_Native.Some (UnfoldAttr a)
           | uu____2442 ->
               (if w
                then
                  (let uu____2456 =
                     let uu____2461 =
                       let uu____2462 = FStar_Syntax_Print.term_to_string t0
                          in
                       FStar_Util.format1 "Not an embedded norm_step: %s"
                         uu____2462
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2461)  in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____2456)
                else ();
                FStar_Pervasives_Native.None))
  
let (unembed_norm_step :
  FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option) =
  fun t  -> __unembed_norm_step true t 
let (unembed_norm_step_safe :
  FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option) =
  fun t  -> __unembed_norm_step false t 
let (embed_range :
  FStar_Range.range -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun r  ->
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
        FStar_Pervasives_Native.None rng
  
let (__unembed_range :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Range.range FStar_Pervasives_Native.option)
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
          FStar_Pervasives_Native.Some r
      | uu____2501 ->
          (if w
           then
             (let uu____2503 =
                let uu____2508 =
                  let uu____2509 = FStar_Syntax_Print.term_to_string t0  in
                  FStar_Util.format1 "Not an embedded range: %s" uu____2509
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____2508)  in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2503)
           else ();
           FStar_Pervasives_Native.None)
  
let (unembed_range :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range FStar_Pervasives_Native.option)
  = fun t  -> __unembed_range true t 
let (unembed_range_safe :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range FStar_Pervasives_Native.option)
  = fun t  -> __unembed_range false t 