open Prims
type 'a embedder = FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
[@@deriving show]
type 'a unembedder =
  FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option[@@deriving
                                                                 show]
let embed_unit: FStar_Range.range -> Prims.unit -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun u  ->
      let uu___38_26 = FStar_Syntax_Util.exp_unit in
      {
        FStar_Syntax_Syntax.n = (uu___38_26.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___38_26.FStar_Syntax_Syntax.vars)
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
      | uu____42 ->
          (if w
           then
             (let uu____44 =
                let uu____49 =
                  let uu____50 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.format1 "Not an embedded unit: %s" uu____50 in
                (FStar_Errors.Warning_NotEmbedded, uu____49) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____44)
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
      let uu___39_81 = t in
      {
        FStar_Syntax_Syntax.n = (uu___39_81.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___39_81.FStar_Syntax_Syntax.vars)
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
      | uu____98 ->
          (if w
           then
             (let uu____100 =
                let uu____105 =
                  let uu____106 = FStar_Syntax_Print.term_to_string t0 in
                  FStar_Util.format1 "Not an embedded bool: %s" uu____106 in
                (FStar_Errors.Warning_NotEmbedded, uu____105) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____100)
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
      let uu___40_134 = t in
      {
        FStar_Syntax_Syntax.n = (uu___40_134.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___40_134.FStar_Syntax_Syntax.vars)
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
      | uu____152 ->
          (if w
           then
             (let uu____154 =
                let uu____159 =
                  let uu____160 = FStar_Syntax_Print.term_to_string t0 in
                  FStar_Util.format1 "Not an embedded char: %s" uu____160 in
                (FStar_Errors.Warning_NotEmbedded, uu____159) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____154)
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
        let uu____189 = FStar_BigInt.string_of_big_int i in
        FStar_Syntax_Util.exp_int uu____189 in
      let uu___41_190 = t in
      {
        FStar_Syntax_Syntax.n = (uu___41_190.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___41_190.FStar_Syntax_Syntax.vars)
      }
let __unembed_int:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____205))
          ->
          let uu____218 = FStar_BigInt.big_int_of_string s in
          FStar_Pervasives_Native.Some uu____218
      | uu____219 ->
          (if w
           then
             (let uu____221 =
                let uu____226 =
                  let uu____227 = FStar_Syntax_Print.term_to_string t0 in
                  FStar_Util.format1 "Not an embedded int: %s" uu____227 in
                (FStar_Errors.Warning_NotEmbedded, uu____226) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____221)
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
                let uu____274 =
                  let uu____275 = FStar_Syntax_Print.term_to_string t0 in
                  FStar_Util.format1 "Not an embedded string: %s" uu____275 in
                (FStar_Errors.Warning_NotEmbedded, uu____274) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____269)
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
              let uu____358 =
                let uu____359 =
                  let uu____360 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.lid_Mktuple2 in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____360
                    [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
                let uu____361 =
                  let uu____362 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____363 =
                    let uu____366 = FStar_Syntax_Syntax.iarg t_b in
                    let uu____367 =
                      let uu____370 =
                        let uu____371 =
                          embed_a rng (FStar_Pervasives_Native.fst x) in
                        FStar_Syntax_Syntax.as_arg uu____371 in
                      let uu____375 =
                        let uu____378 =
                          let uu____379 =
                            embed_b rng (FStar_Pervasives_Native.snd x) in
                          FStar_Syntax_Syntax.as_arg uu____379 in
                        [uu____378] in
                      uu____370 :: uu____375 in
                    uu____366 :: uu____367 in
                  uu____362 :: uu____363 in
                FStar_Syntax_Syntax.mk_Tm_app uu____359 uu____361 in
              uu____358 FStar_Pervasives_Native.None rng
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
          let uu____432 = FStar_Syntax_Util.head_and_args t in
          match uu____432 with
          | (hd1,args) ->
              let uu____475 =
                let uu____488 =
                  let uu____489 = FStar_Syntax_Util.un_uinst hd1 in
                  uu____489.FStar_Syntax_Syntax.n in
                (uu____488, args) in
              (match uu____475 with
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,uu____507::uu____508::(a,uu____510)::(b,uu____512)::[])
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.lid_Mktuple2
                   ->
                   let uu____571 = unembed_a a in
                   FStar_Util.bind_opt uu____571
                     (fun a1  ->
                        let uu____583 = unembed_b b in
                        FStar_Util.bind_opt uu____583
                          (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
               | uu____598 ->
                   (if w
                    then
                      (let uu____612 =
                         let uu____617 =
                           let uu____618 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1 "Not an embedded pair: %s"
                             uu____618 in
                         (FStar_Errors.Warning_NotEmbedded, uu____617) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____612)
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
              let uu____769 =
                let uu____770 =
                  let uu____771 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.none_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____771
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____772 =
                  let uu____773 = FStar_Syntax_Syntax.iarg typ in [uu____773] in
                FStar_Syntax_Syntax.mk_Tm_app uu____770 uu____772 in
              uu____769 FStar_Pervasives_Native.None rng
          | FStar_Pervasives_Native.Some a ->
              let uu____777 =
                let uu____778 =
                  let uu____779 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.some_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____779
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____780 =
                  let uu____781 = FStar_Syntax_Syntax.iarg typ in
                  let uu____782 =
                    let uu____785 =
                      let uu____786 = embed_a rng a in
                      FStar_Syntax_Syntax.as_arg uu____786 in
                    [uu____785] in
                  uu____781 :: uu____782 in
                FStar_Syntax_Syntax.mk_Tm_app uu____778 uu____780 in
              uu____777 FStar_Pervasives_Native.None rng
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
        let uu____822 = FStar_Syntax_Util.head_and_args t in
        match uu____822 with
        | (hd1,args) ->
            let uu____863 =
              let uu____876 =
                let uu____877 = FStar_Syntax_Util.un_uinst hd1 in
                uu____877.FStar_Syntax_Syntax.n in
              (uu____876, args) in
            (match uu____863 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____893) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
                 -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____913::(a,uu____915)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
                 ->
                 let uu____952 = unembed_a a in
                 FStar_Util.bind_opt uu____952
                   (fun a1  ->
                      FStar_Pervasives_Native.Some
                        (FStar_Pervasives_Native.Some a1))
             | uu____963 ->
                 (if w
                  then
                    (let uu____977 =
                       let uu____982 =
                         let uu____983 = FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1 "Not an embedded option: %s"
                           uu____983 in
                       (FStar_Errors.Warning_NotEmbedded, uu____982) in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____977)
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
              let uu____1088 =
                let uu____1089 =
                  let uu____1090 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.nil_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1090
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____1091 =
                  let uu____1092 = FStar_Syntax_Syntax.iarg typ in
                  [uu____1092] in
                FStar_Syntax_Syntax.mk_Tm_app uu____1089 uu____1091 in
              uu____1088 FStar_Pervasives_Native.None rng
          | hd1::tl1 ->
              let uu____1099 =
                let uu____1100 =
                  let uu____1101 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.cons_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1101
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____1102 =
                  let uu____1103 = FStar_Syntax_Syntax.iarg typ in
                  let uu____1104 =
                    let uu____1107 =
                      let uu____1108 = embed_a rng hd1 in
                      FStar_Syntax_Syntax.as_arg uu____1108 in
                    let uu____1112 =
                      let uu____1115 =
                        let uu____1116 =
                          let uu____1117 = embed_list embed_a typ in
                          uu____1117 rng tl1 in
                        FStar_Syntax_Syntax.as_arg uu____1116 in
                      [uu____1115] in
                    uu____1107 :: uu____1112 in
                  uu____1103 :: uu____1104 in
                FStar_Syntax_Syntax.mk_Tm_app uu____1100 uu____1102 in
              uu____1099 FStar_Pervasives_Native.None rng
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
        let uu____1164 = FStar_Syntax_Util.head_and_args t in
        match uu____1164 with
        | (hd1,args) ->
            let uu____1205 =
              let uu____1218 =
                let uu____1219 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1219.FStar_Syntax_Syntax.n in
              (uu____1218, args) in
            (match uu____1205 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1235) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> FStar_Pervasives_Native.Some []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,_t::(hd2,uu____1257)::(tl1,uu____1259)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1306 = unembed_a hd2 in
                 FStar_Util.bind_opt uu____1306
                   (fun hd3  ->
                      let uu____1316 = __unembed_list w unembed_a tl1 in
                      FStar_Util.bind_opt uu____1316
                        (fun tl2  ->
                           FStar_Pervasives_Native.Some (hd3 :: tl2)))
             | uu____1335 ->
                 (if w
                  then
                    (let uu____1349 =
                       let uu____1354 =
                         let uu____1355 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1 "Not an embedded list: %s"
                           uu____1355 in
                       (FStar_Errors.Warning_NotEmbedded, uu____1354) in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1349)
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
      let uu____1434 = embed_list embed_string FStar_Syntax_Syntax.t_string in
      uu____1434 rng ss
let unembed_string_list:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  = fun t  -> let uu____1451 = unembed_list unembed_string in uu____1451 t
let unembed_string_list_safe:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____1467 = unembed_list_safe unembed_string_safe in uu____1467 t
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
    match projectee with | Simpl  -> true | uu____1483 -> false
let uu___is_Weak: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1487 -> false
let uu___is_HNF: norm_step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____1491 -> false
let uu___is_Primops: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1495 -> false
let uu___is_Delta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1499 -> false
let uu___is_Zeta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1503 -> false
let uu___is_Iota: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1507 -> false
let uu___is_UnfoldOnly: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1514 -> false
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
          let uu____1540 =
            let uu____1541 =
              let uu____1542 =
                let uu____1543 =
                  let uu____1544 =
                    embed_list embed_string FStar_Syntax_Syntax.t_string in
                  uu____1544 rng l in
                FStar_Syntax_Syntax.as_arg uu____1543 in
              [uu____1542] in
            FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1541 in
          uu____1540 FStar_Pervasives_Native.None rng
let __unembed_norm_step:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      let uu____1565 = FStar_Syntax_Util.head_and_args t in
      match uu____1565 with
      | (hd1,args) ->
          let uu____1604 =
            let uu____1617 =
              let uu____1618 = FStar_Syntax_Util.un_uinst hd1 in
              uu____1618.FStar_Syntax_Syntax.n in
            (uu____1617, args) in
          (match uu____1604 with
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1738)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_unfoldonly
               ->
               let uu____1763 =
                 let uu____1768 = unembed_list unembed_string in uu____1768 l in
               FStar_Util.bind_opt uu____1763
                 (fun ss  ->
                    FStar_All.pipe_left
                      (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                      (UnfoldOnly ss))
           | uu____1783 ->
               (if w
                then
                  (let uu____1797 =
                     let uu____1802 =
                       let uu____1803 = FStar_Syntax_Print.term_to_string t0 in
                       FStar_Util.format1 "Not an embedded norm_step: %s"
                         uu____1803 in
                     (FStar_Errors.Warning_NotEmbedded, uu____1802) in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____1797)
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
      | uu____1842 ->
          (if w
           then
             (let uu____1844 =
                let uu____1849 =
                  let uu____1850 = FStar_Syntax_Print.term_to_string t0 in
                  FStar_Util.format1 "Not an embedded range: %s" uu____1850 in
                (FStar_Errors.Warning_NotEmbedded, uu____1849) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1844)
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