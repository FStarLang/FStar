open Prims
type 'a embedder = FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
[@@deriving show]
type 'a unembedder =
  FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option[@@deriving
                                                                 show]
let embed_unit: FStar_Range.range -> Prims.unit -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun u  ->
      let uu___262_26 = FStar_Syntax_Util.exp_unit in
      {
        FStar_Syntax_Syntax.n = (uu___262_26.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___262_26.FStar_Syntax_Syntax.vars)
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
      let uu___263_76 = t in
      {
        FStar_Syntax_Syntax.n = (uu___263_76.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___263_76.FStar_Syntax_Syntax.vars)
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
      let uu___264_122 = t in
      {
        FStar_Syntax_Syntax.n = (uu___264_122.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___264_122.FStar_Syntax_Syntax.vars)
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
      | uu____137 ->
          (if w
           then
             (let uu____139 =
                let uu____140 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded char: %s" uu____140 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____139)
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
        let uu____166 = FStar_BigInt.string_of_big_int i in
        FStar_Syntax_Util.exp_int uu____166 in
      let uu___265_167 = t in
      {
        FStar_Syntax_Syntax.n = (uu___265_167.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___265_167.FStar_Syntax_Syntax.vars)
      }
let __unembed_int:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____182))
          ->
          let uu____195 = FStar_BigInt.big_int_of_string s in
          FStar_Pervasives_Native.Some uu____195
      | uu____196 ->
          (if w
           then
             (let uu____198 =
                let uu____199 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded int: %s" uu____199 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____198)
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
          (s,uu____238)) -> FStar_Pervasives_Native.Some s
      | uu____239 ->
          (if w
           then
             (let uu____241 =
                let uu____242 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded string: %s" uu____242 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____241)
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
              let uu____325 =
                let uu____326 =
                  let uu____327 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.lid_Mktuple2 in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____327
                    [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
                let uu____328 =
                  let uu____329 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____330 =
                    let uu____333 = FStar_Syntax_Syntax.iarg t_b in
                    let uu____334 =
                      let uu____337 =
                        let uu____338 =
                          embed_a rng (FStar_Pervasives_Native.fst x) in
                        FStar_Syntax_Syntax.as_arg uu____338 in
                      let uu____342 =
                        let uu____345 =
                          let uu____346 =
                            embed_b rng (FStar_Pervasives_Native.snd x) in
                          FStar_Syntax_Syntax.as_arg uu____346 in
                        [uu____345] in
                      uu____337 :: uu____342 in
                    uu____333 :: uu____334 in
                  uu____329 :: uu____330 in
                FStar_Syntax_Syntax.mk_Tm_app uu____326 uu____328 in
              uu____325 FStar_Pervasives_Native.None rng
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
          let uu____399 = FStar_Syntax_Util.head_and_args t in
          match uu____399 with
          | (hd1,args) ->
              let uu____442 =
                let uu____455 =
                  let uu____456 = FStar_Syntax_Util.un_uinst hd1 in
                  uu____456.FStar_Syntax_Syntax.n in
                (uu____455, args) in
              (match uu____442 with
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,uu____474::uu____475::(a,uu____477)::(b,uu____479)::[])
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.lid_Mktuple2
                   ->
                   let uu____538 = unembed_a a in
                   FStar_Util.bind_opt uu____538
                     (fun a1  ->
                        let uu____550 = unembed_b b in
                        FStar_Util.bind_opt uu____550
                          (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
               | uu____565 ->
                   (if w
                    then
                      (let uu____579 =
                         let uu____580 = FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____580 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____579)
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
              let uu____731 =
                let uu____732 =
                  let uu____733 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.none_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____733
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____734 =
                  let uu____735 = FStar_Syntax_Syntax.iarg typ in [uu____735] in
                FStar_Syntax_Syntax.mk_Tm_app uu____732 uu____734 in
              uu____731 FStar_Pervasives_Native.None rng
          | FStar_Pervasives_Native.Some a ->
              let uu____739 =
                let uu____740 =
                  let uu____741 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.some_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____741
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____742 =
                  let uu____743 = FStar_Syntax_Syntax.iarg typ in
                  let uu____744 =
                    let uu____747 =
                      let uu____748 = embed_a rng a in
                      FStar_Syntax_Syntax.as_arg uu____748 in
                    [uu____747] in
                  uu____743 :: uu____744 in
                FStar_Syntax_Syntax.mk_Tm_app uu____740 uu____742 in
              uu____739 FStar_Pervasives_Native.None rng
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
        let uu____784 = FStar_Syntax_Util.head_and_args t in
        match uu____784 with
        | (hd1,args) ->
            let uu____825 =
              let uu____838 =
                let uu____839 = FStar_Syntax_Util.un_uinst hd1 in
                uu____839.FStar_Syntax_Syntax.n in
              (uu____838, args) in
            (match uu____825 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____855) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
                 -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____875::(a,uu____877)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
                 ->
                 let uu____914 = unembed_a a in
                 FStar_Util.bind_opt uu____914
                   (fun a1  ->
                      FStar_Pervasives_Native.Some
                        (FStar_Pervasives_Native.Some a1))
             | uu____925 ->
                 (if w
                  then
                    (let uu____939 =
                       let uu____940 = FStar_Syntax_Print.term_to_string t0 in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____940 in
                     FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____939)
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
              let uu____1044 =
                let uu____1045 =
                  let uu____1046 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.nil_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1046
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____1047 =
                  let uu____1048 = FStar_Syntax_Syntax.iarg typ in
                  [uu____1048] in
                FStar_Syntax_Syntax.mk_Tm_app uu____1045 uu____1047 in
              uu____1044 FStar_Pervasives_Native.None rng
          | hd1::tl1 ->
              let uu____1055 =
                let uu____1056 =
                  let uu____1057 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.cons_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1057
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____1058 =
                  let uu____1059 = FStar_Syntax_Syntax.iarg typ in
                  let uu____1060 =
                    let uu____1063 =
                      let uu____1064 = embed_a rng hd1 in
                      FStar_Syntax_Syntax.as_arg uu____1064 in
                    let uu____1068 =
                      let uu____1071 =
                        let uu____1072 =
                          let uu____1073 = embed_list embed_a typ in
                          uu____1073 rng tl1 in
                        FStar_Syntax_Syntax.as_arg uu____1072 in
                      [uu____1071] in
                    uu____1063 :: uu____1068 in
                  uu____1059 :: uu____1060 in
                FStar_Syntax_Syntax.mk_Tm_app uu____1056 uu____1058 in
              uu____1055 FStar_Pervasives_Native.None rng
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
        let uu____1119 = FStar_Syntax_Util.head_and_args t in
        match uu____1119 with
        | (hd1,args) ->
            let uu____1160 =
              let uu____1173 =
                let uu____1174 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1174.FStar_Syntax_Syntax.n in
              (uu____1173, args) in
            (match uu____1160 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1190) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> FStar_Pervasives_Native.Some []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,_t::(hd2,uu____1212)::(tl1,uu____1214)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1261 = unembed_a hd2 in
                 FStar_Util.bind_opt uu____1261
                   (fun hd3  ->
                      let uu____1271 = __unembed_list w unembed_a tl1 in
                      FStar_Util.bind_opt uu____1271
                        (fun tl2  ->
                           FStar_Pervasives_Native.Some (hd3 :: tl2)))
             | uu____1290 ->
                 (if w
                  then
                    (let uu____1304 =
                       let uu____1305 = FStar_Syntax_Print.term_to_string t0 in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1305 in
                     FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____1304)
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
      let uu____1384 = embed_list embed_string FStar_Syntax_Syntax.t_string in
      uu____1384 rng ss
let unembed_string_list:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  = fun t  -> let uu____1401 = unembed_list unembed_string in uu____1401 t
let unembed_string_list_safe:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____1417 = unembed_list_safe unembed_string_safe in uu____1417 t
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
    match projectee with | Simpl  -> true | uu____1433 -> false
let uu___is_Weak: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1437 -> false
let uu___is_HNF: norm_step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____1441 -> false
let uu___is_Primops: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1445 -> false
let uu___is_Delta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1449 -> false
let uu___is_Zeta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1453 -> false
let uu___is_Iota: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1457 -> false
let uu___is_UnfoldOnly: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1464 -> false
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
          let uu____1490 =
            let uu____1491 =
              let uu____1492 =
                let uu____1493 =
                  let uu____1494 =
                    embed_list embed_string FStar_Syntax_Syntax.t_string in
                  uu____1494 rng l in
                FStar_Syntax_Syntax.as_arg uu____1493 in
              [uu____1492] in
            FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1491 in
          uu____1490 FStar_Pervasives_Native.None rng
let __unembed_norm_step:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t0  ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      let uu____1515 = FStar_Syntax_Util.head_and_args t in
      match uu____1515 with
      | (hd1,args) ->
          let uu____1554 =
            let uu____1567 =
              let uu____1568 = FStar_Syntax_Util.un_uinst hd1 in
              uu____1568.FStar_Syntax_Syntax.n in
            (uu____1567, args) in
          (match uu____1554 with
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1688)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_unfoldonly
               ->
               let uu____1713 =
                 let uu____1718 = unembed_list unembed_string in uu____1718 l in
               FStar_Util.bind_opt uu____1713
                 (fun ss  ->
                    FStar_All.pipe_left
                      (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                      (UnfoldOnly ss))
           | uu____1733 ->
               (if w
                then
                  (let uu____1747 =
                     let uu____1748 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____1748 in
                   FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____1747)
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
      | uu____1787 ->
          (if w
           then
             (let uu____1789 =
                let uu____1790 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded range: %s" uu____1790 in
              FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____1789)
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