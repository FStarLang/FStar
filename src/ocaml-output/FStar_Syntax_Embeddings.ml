open Prims
type 'a embedder = FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
[@@deriving show]
type 'a unembedder =
  FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option[@@deriving
                                                                 show]
let embed_unit: FStar_Range.range -> Prims.unit -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun u  ->
      let uu___221_28 = FStar_Syntax_Util.exp_unit in
      {
        FStar_Syntax_Syntax.n = (uu___221_28.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___221_28.FStar_Syntax_Syntax.vars)
      }
let __unembed_unit:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unascribe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
          FStar_Pervasives_Native.Some ()
      | uu____46 ->
          (if w
           then
             (let uu____48 =
                let uu____49 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded unit: %s" uu____49 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____48)
           else ();
           FStar_Pervasives_Native.None)
let unembed_unit:
  FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option =
  fun t  -> __unembed_unit true t
let unembed_unit_safe:
  FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option =
  fun t  -> __unembed_unit false t
let embed_bool: FStar_Range.range -> Prims.bool -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun b  ->
      let t =
        if b
        then FStar_Syntax_Util.exp_true_bool
        else FStar_Syntax_Util.exp_false_bool in
      let uu___222_84 = t in
      {
        FStar_Syntax_Syntax.n = (uu___222_84.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___222_84.FStar_Syntax_Syntax.vars)
      }
let __unembed_bool:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
          FStar_Pervasives_Native.Some b
      | uu____103 ->
          (if w
           then
             (let uu____105 =
                let uu____106 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded bool: %s" uu____106 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____105)
           else ();
           FStar_Pervasives_Native.None)
let unembed_bool:
  FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option =
  fun t  -> __unembed_bool true t
let unembed_bool_safe:
  FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option =
  fun t  -> __unembed_bool false t
let embed_char:
  FStar_Range.range -> FStar_Char.char -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun c  ->
      let t = FStar_Syntax_Util.exp_char c in
      let uu___223_136 = t in
      {
        FStar_Syntax_Syntax.n = (uu___223_136.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___223_136.FStar_Syntax_Syntax.vars)
      }
let __unembed_char:
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Char.char FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
          FStar_Pervasives_Native.Some c
      | uu____153 ->
          (if w
           then
             (let uu____155 =
                let uu____156 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded char: %s" uu____156 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____155)
           else ();
           FStar_Pervasives_Native.None)
let unembed_char:
  FStar_Syntax_Syntax.term -> FStar_Char.char FStar_Pervasives_Native.option
  = fun t  -> __unembed_char true t
let unembed_char_safe:
  FStar_Syntax_Syntax.term -> FStar_Char.char FStar_Pervasives_Native.option
  = fun t  -> __unembed_char false t
let embed_int:
  FStar_Range.range -> FStar_BigInt.t -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun i  ->
      let t =
        let uu____186 = FStar_BigInt.string_of_big_int i in
        FStar_Syntax_Util.exp_int uu____186 in
      let uu___224_187 = t in
      {
        FStar_Syntax_Syntax.n = (uu___224_187.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___224_187.FStar_Syntax_Syntax.vars)
      }
let __unembed_int:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____204))
          ->
          let uu____217 = FStar_BigInt.big_int_of_string s in
          FStar_Pervasives_Native.Some uu____217
      | uu____218 ->
          (if w
           then
             (let uu____220 =
                let uu____221 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded int: %s" uu____221 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____220)
           else ();
           FStar_Pervasives_Native.None)
let unembed_int:
  FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option =
  fun t  -> __unembed_int true t
let unembed_int_safe:
  FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option =
  fun t  -> __unembed_int false t
let embed_string:
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun s  ->
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
        FStar_Pervasives_Native.None rng
let __unembed_string:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
          (s,uu____266)) -> FStar_Pervasives_Native.Some s
      | uu____267 ->
          (if w
           then
             (let uu____269 =
                let uu____270 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded string: %s" uu____270 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____269)
           else ();
           FStar_Pervasives_Native.None)
let unembed_string:
  FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option =
  fun t  -> __unembed_string true t
let unembed_string_safe:
  FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option =
  fun t  -> __unembed_string false t
let embed_pair:
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
              let uu____361 =
                let uu____362 =
                  let uu____363 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.lid_Mktuple2 in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____363
                    [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
                let uu____364 =
                  let uu____365 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____366 =
                    let uu____369 = FStar_Syntax_Syntax.iarg t_b in
                    let uu____370 =
                      let uu____373 =
                        let uu____374 =
                          embed_a rng (FStar_Pervasives_Native.fst x) in
                        FStar_Syntax_Syntax.as_arg uu____374 in
                      let uu____378 =
                        let uu____381 =
                          let uu____382 =
                            embed_b rng (FStar_Pervasives_Native.snd x) in
                          FStar_Syntax_Syntax.as_arg uu____382 in
                        [uu____381] in
                      uu____373 :: uu____378 in
                    uu____369 :: uu____370 in
                  uu____365 :: uu____366 in
                FStar_Syntax_Syntax.mk_Tm_app uu____362 uu____364 in
              uu____361 FStar_Pervasives_Native.None rng
let __unembed_pair:
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
          let t = FStar_Syntax_Util.unmeta_safe t0 in
          let uu____441 = FStar_Syntax_Util.head_and_args t in
          match uu____441 with
          | (hd1,args) ->
              let uu____484 =
                let uu____497 =
                  let uu____498 = FStar_Syntax_Util.un_uinst hd1 in
                  uu____498.FStar_Syntax_Syntax.n in
                (uu____497, args) in
              (match uu____484 with
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,uu____516::uu____517::(a,uu____519)::(b,uu____521)::[])
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.lid_Mktuple2
                   ->
                   let uu____580 = unembed_a a in
                   FStar_Util.bind_opt uu____580
                     (fun a1  ->
                        let uu____592 = unembed_b b in
                        FStar_Util.bind_opt uu____592
                          (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
               | uu____607 ->
                   (if w
                    then
                      (let uu____621 =
                         let uu____622 = FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____622 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____621)
                    else ();
                    FStar_Pervasives_Native.None))
let unembed_pair:
  'a 'b .
    'a unembedder ->
      'b unembedder -> ('a,'b) FStar_Pervasives_Native.tuple2 unembedder
  = fun ul  -> fun ur  -> fun t  -> __unembed_pair true ul ur t
let unembed_pair_safe:
  'a 'b .
    'a unembedder ->
      'b unembedder -> ('a,'b) FStar_Pervasives_Native.tuple2 unembedder
  = fun ul  -> fun ur  -> fun t  -> __unembed_pair false ul ur t
let embed_option:
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
              let uu____784 =
                let uu____785 =
                  let uu____786 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.none_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____786
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____787 =
                  let uu____788 = FStar_Syntax_Syntax.iarg typ in [uu____788] in
                FStar_Syntax_Syntax.mk_Tm_app uu____785 uu____787 in
              uu____784 FStar_Pervasives_Native.None rng
          | FStar_Pervasives_Native.Some a ->
              let uu____792 =
                let uu____793 =
                  let uu____794 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.some_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____794
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____795 =
                  let uu____796 = FStar_Syntax_Syntax.iarg typ in
                  let uu____797 =
                    let uu____800 =
                      let uu____801 = embed_a rng a in
                      FStar_Syntax_Syntax.as_arg uu____801 in
                    [uu____800] in
                  uu____796 :: uu____797 in
                FStar_Syntax_Syntax.mk_Tm_app uu____793 uu____795 in
              uu____792 FStar_Pervasives_Native.None rng
let __unembed_option:
  'a .
    Prims.bool ->
      'a unembedder ->
        FStar_Syntax_Syntax.term ->
          'a FStar_Pervasives_Native.option FStar_Pervasives_Native.option
  =
  fun w  ->
    fun unembed_a  ->
      fun t0  ->
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        let uu____841 = FStar_Syntax_Util.head_and_args t in
        match uu____841 with
        | (hd1,args) ->
            let uu____882 =
              let uu____895 =
                let uu____896 = FStar_Syntax_Util.un_uinst hd1 in
                uu____896.FStar_Syntax_Syntax.n in
              (uu____895, args) in
            (match uu____882 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____912) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
                 -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____932::(a,uu____934)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
                 ->
                 let uu____971 = unembed_a a in
                 FStar_Util.bind_opt uu____971
                   (fun a1  ->
                      FStar_Pervasives_Native.Some
                        (FStar_Pervasives_Native.Some a1))
             | uu____982 ->
                 (if w
                  then
                    (let uu____996 =
                       let uu____997 = FStar_Syntax_Print.term_to_string t0 in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____997 in
                     FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____996)
                  else ();
                  FStar_Pervasives_Native.None))
let unembed_option:
  'a . 'a unembedder -> 'a FStar_Pervasives_Native.option unembedder =
  fun ua  -> fun t  -> __unembed_option true ua t
let unembed_option_safe:
  'a . 'a unembedder -> 'a FStar_Pervasives_Native.option unembedder =
  fun ua  -> fun t  -> __unembed_option false ua t
let rec embed_list:
  'a . 'a embedder -> FStar_Syntax_Syntax.typ -> 'a Prims.list embedder =
  fun embed_a  ->
    fun typ  ->
      fun rng  ->
        fun l  ->
          match l with
          | [] ->
              let uu____1108 =
                let uu____1109 =
                  let uu____1110 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.nil_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1110
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____1111 =
                  let uu____1112 = FStar_Syntax_Syntax.iarg typ in
                  [uu____1112] in
                FStar_Syntax_Syntax.mk_Tm_app uu____1109 uu____1111 in
              uu____1108 FStar_Pervasives_Native.None rng
          | hd1::tl1 ->
              let uu____1119 =
                let uu____1120 =
                  let uu____1121 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.cons_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1121
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____1122 =
                  let uu____1123 = FStar_Syntax_Syntax.iarg typ in
                  let uu____1124 =
                    let uu____1127 =
                      let uu____1128 = embed_a rng hd1 in
                      FStar_Syntax_Syntax.as_arg uu____1128 in
                    let uu____1132 =
                      let uu____1135 =
                        let uu____1136 =
                          let uu____1137 = embed_list embed_a typ in
                          uu____1137 rng tl1 in
                        FStar_Syntax_Syntax.as_arg uu____1136 in
                      [uu____1135] in
                    uu____1127 :: uu____1132 in
                  uu____1123 :: uu____1124 in
                FStar_Syntax_Syntax.mk_Tm_app uu____1120 uu____1122 in
              uu____1119 FStar_Pervasives_Native.None rng
let rec __unembed_list:
  'a .
    Prims.bool ->
      'a unembedder ->
        FStar_Syntax_Syntax.term ->
          'a Prims.list FStar_Pervasives_Native.option
  =
  fun w  ->
    fun unembed_a  ->
      fun t0  ->
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        let uu____1187 = FStar_Syntax_Util.head_and_args t in
        match uu____1187 with
        | (hd1,args) ->
            let uu____1228 =
              let uu____1241 =
                let uu____1242 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1242.FStar_Syntax_Syntax.n in
              (uu____1241, args) in
            (match uu____1228 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1258) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> FStar_Pervasives_Native.Some []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,_t::(hd2,uu____1280)::(tl1,uu____1282)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1329 = unembed_a hd2 in
                 FStar_Util.bind_opt uu____1329
                   (fun hd3  ->
                      let uu____1339 = __unembed_list w unembed_a tl1 in
                      FStar_Util.bind_opt uu____1339
                        (fun tl2  ->
                           FStar_Pervasives_Native.Some (hd3 :: tl2)))
             | uu____1358 ->
                 (if w
                  then
                    (let uu____1372 =
                       let uu____1373 = FStar_Syntax_Print.term_to_string t0 in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1373 in
                     FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____1372)
                  else ();
                  FStar_Pervasives_Native.None))
let unembed_list: 'a . 'a unembedder -> 'a Prims.list unembedder =
  fun ua  -> fun t  -> __unembed_list true ua t
let unembed_list_safe: 'a . 'a unembedder -> 'a Prims.list unembedder =
  fun ua  -> fun t  -> __unembed_list false ua t
let embed_string_list:
  FStar_Range.range -> Prims.string Prims.list -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun ss  ->
      let uu____1458 = embed_list embed_string FStar_Syntax_Syntax.t_string in
      uu____1458 rng ss
let unembed_string_list:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  = fun t  -> let uu____1476 = unembed_list unembed_string in uu____1476 t
let unembed_string_list_safe:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____1493 = unembed_list_safe unembed_string_safe in uu____1493 t
type norm_step =
  | Simpl
  | Weak
  | HNF
  | Primops
  | Delta
  | Zeta
  | Iota
  | UnfoldOnly of Prims.string Prims.list[@@deriving show]
let uu___is_Simpl: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____1510 -> false
let uu___is_Weak: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1515 -> false
let uu___is_HNF: norm_step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____1520 -> false
let uu___is_Primops: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1525 -> false
let uu___is_Delta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1530 -> false
let uu___is_Zeta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1535 -> false
let uu___is_Iota: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1540 -> false
let uu___is_UnfoldOnly: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1548 -> false
let __proj__UnfoldOnly__item___0: norm_step -> Prims.string Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let steps_Simpl: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_simpl
let steps_Weak: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_weak
let steps_HNF: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_hnf
let steps_Primops: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_primops
let steps_Delta: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_delta
let steps_Zeta: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_zeta
let steps_Iota: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_iota
let steps_UnfoldOnly: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly
let embed_norm_step:
  FStar_Range.range -> norm_step -> FStar_Syntax_Syntax.term =
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
          let uu____1577 =
            let uu____1578 =
              let uu____1579 =
                let uu____1580 =
                  let uu____1581 =
                    embed_list embed_string FStar_Syntax_Syntax.t_string in
                  uu____1581 rng l in
                FStar_Syntax_Syntax.as_arg uu____1580 in
              [uu____1579] in
            FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1578 in
          uu____1577 FStar_Pervasives_Native.None rng
let __unembed_norm_step:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      let uu____1604 = FStar_Syntax_Util.head_and_args t in
      match uu____1604 with
      | (hd1,args) ->
          let uu____1643 =
            let uu____1656 =
              let uu____1657 = FStar_Syntax_Util.un_uinst hd1 in
              uu____1657.FStar_Syntax_Syntax.n in
            (uu____1656, args) in
          (match uu____1643 with
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1777)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_unfoldonly
               ->
               let uu____1802 =
                 let uu____1807 = unembed_list unembed_string in uu____1807 l in
               FStar_Util.bind_opt uu____1802
                 (fun ss  ->
                    FStar_All.pipe_left
                      (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                      (UnfoldOnly ss))
           | uu____1822 ->
               (if w
                then
                  (let uu____1836 =
                     let uu____1837 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____1837 in
                   FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____1836)
                else ();
                FStar_Pervasives_Native.None))
let unembed_norm_step:
  FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option =
  fun t  -> __unembed_norm_step true t
let unembed_norm_step_safe:
  FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option =
  fun t  -> __unembed_norm_step false t
let embed_range:
  FStar_Range.range -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun r  ->
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
        FStar_Pervasives_Native.None rng
let __unembed_range:
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Range.range FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
          FStar_Pervasives_Native.Some r
      | uu____1882 ->
          (if w
           then
             (let uu____1884 =
                let uu____1885 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded range: %s" uu____1885 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____1884)
           else ();
           FStar_Pervasives_Native.None)
let unembed_range:
  FStar_Syntax_Syntax.term ->
    FStar_Range.range FStar_Pervasives_Native.option
  = fun t  -> __unembed_range true t
let unembed_range_safe:
  FStar_Syntax_Syntax.term ->
    FStar_Range.range FStar_Pervasives_Native.option
  = fun t  -> __unembed_range false t