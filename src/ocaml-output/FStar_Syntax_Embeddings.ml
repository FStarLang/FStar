open Prims
type 'a embedder = FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
[@@deriving show]
type 'a unembedder =
  FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option[@@deriving
                                                                 show]
let embed_unit: FStar_Range.range -> Prims.unit -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun u  ->
      let uu___111_26 = FStar_Syntax_Util.exp_unit in
      {
        FStar_Syntax_Syntax.n = (uu___111_26.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___111_26.FStar_Syntax_Syntax.vars)
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
                let uu____45 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded unit: %s" uu____45 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____44)
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
      let uu___112_76 = t in
      {
        FStar_Syntax_Syntax.n = (uu___112_76.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___112_76.FStar_Syntax_Syntax.vars)
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
      | uu____93 ->
          (if w
           then
             (let uu____95 =
                let uu____96 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded bool: %s" uu____96 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____95)
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
      let uu___113_137 = t in
      {
        FStar_Syntax_Syntax.n = (uu___113_137.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___113_137.FStar_Syntax_Syntax.vars)
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
      | uu____158 ->
          (if w
           then
             (let uu____160 =
                let uu____161 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded char: %s" uu____161 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____160)
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
        let uu____187 = FStar_BigInt.string_of_big_int i in
        FStar_Syntax_Util.exp_int uu____187 in
      let uu___114_188 = t in
      {
        FStar_Syntax_Syntax.n = (uu___114_188.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___114_188.FStar_Syntax_Syntax.vars)
      }
let __unembed_int:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____203))
          ->
          let uu____216 = FStar_BigInt.big_int_of_string s in
          FStar_Pervasives_Native.Some uu____216
      | uu____217 ->
          (if w
           then
             (let uu____219 =
                let uu____220 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded int: %s" uu____220 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____219)
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
          (s,uu____259)) -> FStar_Pervasives_Native.Some s
      | uu____260 ->
          (if w
           then
             (let uu____262 =
                let uu____263 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded string: %s" uu____263 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____262)
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
              let uu____346 =
                let uu____347 =
                  let uu____348 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.lid_Mktuple2 in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____348
                    [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
                let uu____349 =
                  let uu____350 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____351 =
                    let uu____354 = FStar_Syntax_Syntax.iarg t_b in
                    let uu____355 =
                      let uu____358 =
                        let uu____359 =
                          embed_a rng (FStar_Pervasives_Native.fst x) in
                        FStar_Syntax_Syntax.as_arg uu____359 in
                      let uu____363 =
                        let uu____366 =
                          let uu____367 =
                            embed_b rng (FStar_Pervasives_Native.snd x) in
                          FStar_Syntax_Syntax.as_arg uu____367 in
                        [uu____366] in
                      uu____358 :: uu____363 in
                    uu____354 :: uu____355 in
                  uu____350 :: uu____351 in
                FStar_Syntax_Syntax.mk_Tm_app uu____347 uu____349 in
              uu____346 FStar_Pervasives_Native.None rng
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
          let uu____420 = FStar_Syntax_Util.head_and_args t in
          match uu____420 with
          | (hd1,args) ->
              let uu____463 =
                let uu____476 =
                  let uu____477 = FStar_Syntax_Util.un_uinst hd1 in
                  uu____477.FStar_Syntax_Syntax.n in
                (uu____476, args) in
              (match uu____463 with
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,uu____495::uu____496::(a,uu____498)::(b,uu____500)::[])
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.lid_Mktuple2
                   ->
                   let uu____559 = unembed_a a in
                   FStar_Util.bind_opt uu____559
                     (fun a1  ->
                        let uu____571 = unembed_b b in
                        FStar_Util.bind_opt uu____571
                          (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
               | uu____586 ->
                   (if w
                    then
                      (let uu____600 =
                         let uu____601 = FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____601 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____600)
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
              let uu____752 =
                let uu____753 =
                  let uu____754 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.none_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____754
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____755 =
                  let uu____756 = FStar_Syntax_Syntax.iarg typ in [uu____756] in
                FStar_Syntax_Syntax.mk_Tm_app uu____753 uu____755 in
              uu____752 FStar_Pervasives_Native.None rng
          | FStar_Pervasives_Native.Some a ->
              let uu____760 =
                let uu____761 =
                  let uu____762 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.some_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____762
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____763 =
                  let uu____764 = FStar_Syntax_Syntax.iarg typ in
                  let uu____765 =
                    let uu____768 =
                      let uu____769 = embed_a rng a in
                      FStar_Syntax_Syntax.as_arg uu____769 in
                    [uu____768] in
                  uu____764 :: uu____765 in
                FStar_Syntax_Syntax.mk_Tm_app uu____761 uu____763 in
              uu____760 FStar_Pervasives_Native.None rng
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
        let uu____805 = FStar_Syntax_Util.head_and_args t in
        match uu____805 with
        | (hd1,args) ->
            let uu____846 =
              let uu____859 =
                let uu____860 = FStar_Syntax_Util.un_uinst hd1 in
                uu____860.FStar_Syntax_Syntax.n in
              (uu____859, args) in
            (match uu____846 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____876) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
                 -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____896::(a,uu____898)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
                 ->
                 let uu____935 = unembed_a a in
                 FStar_Util.bind_opt uu____935
                   (fun a1  ->
                      FStar_Pervasives_Native.Some
                        (FStar_Pervasives_Native.Some a1))
             | uu____946 ->
                 (if w
                  then
                    (let uu____960 =
                       let uu____961 = FStar_Syntax_Print.term_to_string t0 in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____961 in
                     FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____960)
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
              let uu____1066 =
                let uu____1067 =
                  let uu____1068 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.nil_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1068
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____1069 =
                  let uu____1070 = FStar_Syntax_Syntax.iarg typ in
                  [uu____1070] in
                FStar_Syntax_Syntax.mk_Tm_app uu____1067 uu____1069 in
              uu____1066 FStar_Pervasives_Native.None rng
          | hd1::tl1 ->
              let uu____1077 =
                let uu____1078 =
                  let uu____1079 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.cons_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1079
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____1080 =
                  let uu____1081 = FStar_Syntax_Syntax.iarg typ in
                  let uu____1082 =
                    let uu____1085 =
                      let uu____1086 = embed_a rng hd1 in
                      FStar_Syntax_Syntax.as_arg uu____1086 in
                    let uu____1090 =
                      let uu____1093 =
                        let uu____1094 =
                          let uu____1095 = embed_list embed_a typ in
                          uu____1095 rng tl1 in
                        FStar_Syntax_Syntax.as_arg uu____1094 in
                      [uu____1093] in
                    uu____1085 :: uu____1090 in
                  uu____1081 :: uu____1082 in
                FStar_Syntax_Syntax.mk_Tm_app uu____1078 uu____1080 in
              uu____1077 FStar_Pervasives_Native.None rng
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
        let uu____1142 = FStar_Syntax_Util.head_and_args t in
        match uu____1142 with
        | (hd1,args) ->
            let uu____1183 =
              let uu____1196 =
                let uu____1197 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1197.FStar_Syntax_Syntax.n in
              (uu____1196, args) in
            (match uu____1183 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1213) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> FStar_Pervasives_Native.Some []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,_t::(hd2,uu____1235)::(tl1,uu____1237)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1284 = unembed_a hd2 in
                 FStar_Util.bind_opt uu____1284
                   (fun hd3  ->
                      let uu____1294 = __unembed_list w unembed_a tl1 in
                      FStar_Util.bind_opt uu____1294
                        (fun tl2  ->
                           FStar_Pervasives_Native.Some (hd3 :: tl2)))
             | uu____1313 ->
                 (if w
                  then
                    (let uu____1327 =
                       let uu____1328 = FStar_Syntax_Print.term_to_string t0 in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1328 in
                     FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____1327)
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
      let uu____1407 = embed_list embed_string FStar_Syntax_Syntax.t_string in
      uu____1407 rng ss
let unembed_string_list:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  = fun t  -> let uu____1424 = unembed_list unembed_string in uu____1424 t
let unembed_string_list_safe:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____1440 = unembed_list_safe unembed_string_safe in uu____1440 t
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
    match projectee with | Simpl  -> true | uu____1456 -> false
let uu___is_Weak: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1460 -> false
let uu___is_HNF: norm_step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____1464 -> false
let uu___is_Primops: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1468 -> false
let uu___is_Delta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1472 -> false
let uu___is_Zeta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1476 -> false
let uu___is_Iota: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1480 -> false
let uu___is_UnfoldOnly: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1487 -> false
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
          let uu____1513 =
            let uu____1514 =
              let uu____1515 =
                let uu____1516 =
                  let uu____1517 =
                    embed_list embed_string FStar_Syntax_Syntax.t_string in
                  uu____1517 rng l in
                FStar_Syntax_Syntax.as_arg uu____1516 in
              [uu____1515] in
            FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1514 in
          uu____1513 FStar_Pervasives_Native.None rng
let __unembed_norm_step:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      let uu____1538 = FStar_Syntax_Util.head_and_args t in
      match uu____1538 with
      | (hd1,args) ->
          let uu____1577 =
            let uu____1590 =
              let uu____1591 = FStar_Syntax_Util.un_uinst hd1 in
              uu____1591.FStar_Syntax_Syntax.n in
            (uu____1590, args) in
          (match uu____1577 with
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1711)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_unfoldonly
               ->
               let uu____1736 =
                 let uu____1741 = unembed_list unembed_string in uu____1741 l in
               FStar_Util.bind_opt uu____1736
                 (fun ss  ->
                    FStar_All.pipe_left
                      (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                      (UnfoldOnly ss))
           | uu____1756 ->
               (if w
                then
                  (let uu____1770 =
                     let uu____1771 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____1771 in
                   FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____1770)
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
      | uu____1810 ->
          (if w
           then
             (let uu____1812 =
                let uu____1813 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded range: %s" uu____1813 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____1812)
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