open Prims
type 'a embedder = FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
[@@deriving show]
type 'a unembedder =
  FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option[@@deriving
                                                                 show]
let embed_unit: FStar_Range.range -> Prims.unit -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun u  ->
      let uu___213_28 = FStar_Syntax_Util.exp_unit in
      {
        FStar_Syntax_Syntax.n = (uu___213_28.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___213_28.FStar_Syntax_Syntax.vars)
      }
let __unembed_unit:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unascribe t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
          FStar_Pervasives_Native.Some ()
      | uu____46 ->
          (if w
           then
             (let uu____48 =
                let uu____49 = FStar_Syntax_Print.term_to_string t1 in
                FStar_Util.format1 "Not an embedded unit: %s" uu____49 in
              FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____48)
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
      let uu___214_84 = t in
      {
        FStar_Syntax_Syntax.n = (uu___214_84.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___214_84.FStar_Syntax_Syntax.vars)
      }
let __unembed_bool:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t  ->
      let uu____99 =
        let uu____100 =
          let uu____103 = FStar_Syntax_Util.unmeta t in
          FStar_Syntax_Subst.compress uu____103 in
        uu____100.FStar_Syntax_Syntax.n in
      match uu____99 with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
          FStar_Pervasives_Native.Some b
      | uu____107 ->
          (if w
           then
             (let uu____109 =
                let uu____110 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded bool: %s" uu____110 in
              FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____109)
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
      let uu___215_140 = t in
      {
        FStar_Syntax_Syntax.n = (uu___215_140.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___215_140.FStar_Syntax_Syntax.vars)
      }
let __unembed_char:
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Char.char FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t  ->
      let uu____153 =
        let uu____154 =
          let uu____157 = FStar_Syntax_Util.unmeta t in
          FStar_Syntax_Subst.compress uu____157 in
        uu____154.FStar_Syntax_Syntax.n in
      match uu____153 with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
          FStar_Pervasives_Native.Some c
      | uu____161 ->
          (if w
           then
             (let uu____163 =
                let uu____164 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded char: %s" uu____164 in
              FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____163)
           else ();
           FStar_Pervasives_Native.None)
let unembed_char:
  FStar_Syntax_Syntax.term -> FStar_Char.char FStar_Pervasives_Native.option
  = fun t  -> __unembed_char true t
let unembed_char_safe:
  FStar_Syntax_Syntax.term -> FStar_Char.char FStar_Pervasives_Native.option
  = fun t  -> __unembed_char false t
let embed_int: FStar_Range.range -> Prims.int -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun i  ->
      let t =
        let uu____194 = FStar_Util.string_of_int i in
        FStar_Syntax_Util.exp_int uu____194 in
      let uu___216_195 = t in
      {
        FStar_Syntax_Syntax.n = (uu___216_195.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___216_195.FStar_Syntax_Syntax.vars)
      }
let __unembed_int:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.int FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t  ->
      let uu____208 =
        let uu____209 =
          let uu____212 = FStar_Syntax_Util.unmeta t in
          FStar_Syntax_Subst.compress uu____212 in
        uu____209.FStar_Syntax_Syntax.n in
      match uu____208 with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____216))
          ->
          let uu____229 = FStar_Util.int_of_string s in
          FStar_Pervasives_Native.Some uu____229
      | uu____230 ->
          (if w
           then
             (let uu____232 =
                let uu____233 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded int: %s" uu____233 in
              FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____232)
           else ();
           FStar_Pervasives_Native.None)
let unembed_int:
  FStar_Syntax_Syntax.term -> Prims.int FStar_Pervasives_Native.option =
  fun t  -> __unembed_int true t
let unembed_int_safe:
  FStar_Syntax_Syntax.term -> Prims.int FStar_Pervasives_Native.option =
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
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
          (s,uu____278)) -> FStar_Pervasives_Native.Some s
      | uu____279 ->
          (if w
           then
             (let uu____281 =
                let uu____282 = FStar_Syntax_Print.term_to_string t1 in
                FStar_Util.format1 "Not an embedded string: %s" uu____282 in
              FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____281)
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
              let uu____373 =
                let uu____374 =
                  let uu____375 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.lid_Mktuple2 in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____375
                    [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
                let uu____376 =
                  let uu____377 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____378 =
                    let uu____381 = FStar_Syntax_Syntax.iarg t_b in
                    let uu____382 =
                      let uu____385 =
                        let uu____386 =
                          embed_a rng (FStar_Pervasives_Native.fst x) in
                        FStar_Syntax_Syntax.as_arg uu____386 in
                      let uu____390 =
                        let uu____393 =
                          let uu____394 =
                            embed_b rng (FStar_Pervasives_Native.snd x) in
                          FStar_Syntax_Syntax.as_arg uu____394 in
                        [uu____393] in
                      uu____385 :: uu____390 in
                    uu____381 :: uu____382 in
                  uu____377 :: uu____378 in
                FStar_Syntax_Syntax.mk_Tm_app uu____374 uu____376 in
              uu____373 FStar_Pervasives_Native.None rng
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
        fun t  ->
          let t1 = FStar_Syntax_Util.unmeta t in
          let uu____453 = FStar_Syntax_Util.head_and_args t1 in
          match uu____453 with
          | (hd1,args) ->
              let uu____496 =
                let uu____509 =
                  let uu____510 = FStar_Syntax_Util.un_uinst hd1 in
                  uu____510.FStar_Syntax_Syntax.n in
                (uu____509, args) in
              (match uu____496 with
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,uu____528::uu____529::(a,uu____531)::(b,uu____533)::[])
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.lid_Mktuple2
                   ->
                   let uu____592 = unembed_a a in
                   FStar_Util.bind_opt uu____592
                     (fun a1  ->
                        let uu____604 = unembed_b b in
                        FStar_Util.bind_opt uu____604
                          (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
               | uu____619 ->
                   (if w
                    then
                      (let uu____633 =
                         let uu____634 = FStar_Syntax_Print.term_to_string t1 in
                         FStar_Util.format1 "Not an embedded pair: %s"
                           uu____634 in
                       FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____633)
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
              let uu____796 =
                let uu____797 =
                  let uu____798 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.none_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____798
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____799 =
                  let uu____800 = FStar_Syntax_Syntax.iarg typ in [uu____800] in
                FStar_Syntax_Syntax.mk_Tm_app uu____797 uu____799 in
              uu____796 FStar_Pervasives_Native.None rng
          | FStar_Pervasives_Native.Some a ->
              let uu____804 =
                let uu____805 =
                  let uu____806 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.some_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____806
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____807 =
                  let uu____808 = FStar_Syntax_Syntax.iarg typ in
                  let uu____809 =
                    let uu____812 =
                      let uu____813 = embed_a rng a in
                      FStar_Syntax_Syntax.as_arg uu____813 in
                    [uu____812] in
                  uu____808 :: uu____809 in
                FStar_Syntax_Syntax.mk_Tm_app uu____805 uu____807 in
              uu____804 FStar_Pervasives_Native.None rng
let __unembed_option:
  'a .
    Prims.bool ->
      'a unembedder ->
        FStar_Syntax_Syntax.term ->
          'a FStar_Pervasives_Native.option FStar_Pervasives_Native.option
  =
  fun w  ->
    fun unembed_a  ->
      fun t  ->
        let uu____852 =
          let uu____867 = FStar_Syntax_Util.unmeta t in
          FStar_Syntax_Util.head_and_args uu____867 in
        match uu____852 with
        | (hd1,args) ->
            let uu____894 =
              let uu____907 =
                let uu____908 = FStar_Syntax_Util.un_uinst hd1 in
                uu____908.FStar_Syntax_Syntax.n in
              (uu____907, args) in
            (match uu____894 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____924) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
                 -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____944::(a,uu____946)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
                 ->
                 let uu____983 = unembed_a a in
                 FStar_Util.bind_opt uu____983
                   (fun a1  ->
                      FStar_Pervasives_Native.Some
                        (FStar_Pervasives_Native.Some a1))
             | uu____994 ->
                 (if w
                  then
                    (let uu____1008 =
                       let uu____1009 = FStar_Syntax_Print.term_to_string t in
                       FStar_Util.format1 "Not an embedded option: %s"
                         uu____1009 in
                     FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____1008)
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
              let uu____1120 =
                let uu____1121 =
                  let uu____1122 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.nil_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1122
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____1123 =
                  let uu____1124 = FStar_Syntax_Syntax.iarg typ in
                  [uu____1124] in
                FStar_Syntax_Syntax.mk_Tm_app uu____1121 uu____1123 in
              uu____1120 FStar_Pervasives_Native.None rng
          | hd1::tl1 ->
              let uu____1131 =
                let uu____1132 =
                  let uu____1133 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.cons_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____1133
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____1134 =
                  let uu____1135 = FStar_Syntax_Syntax.iarg typ in
                  let uu____1136 =
                    let uu____1139 =
                      let uu____1140 = embed_a rng hd1 in
                      FStar_Syntax_Syntax.as_arg uu____1140 in
                    let uu____1144 =
                      let uu____1147 =
                        let uu____1148 =
                          let uu____1149 = embed_list embed_a typ in
                          uu____1149 rng tl1 in
                        FStar_Syntax_Syntax.as_arg uu____1148 in
                      [uu____1147] in
                    uu____1139 :: uu____1144 in
                  uu____1135 :: uu____1136 in
                FStar_Syntax_Syntax.mk_Tm_app uu____1132 uu____1134 in
              uu____1131 FStar_Pervasives_Native.None rng
let rec __unembed_list:
  'a .
    Prims.bool ->
      'a unembedder ->
        FStar_Syntax_Syntax.term ->
          'a Prims.list FStar_Pervasives_Native.option
  =
  fun w  ->
    fun unembed_a  ->
      fun t  ->
        let t1 = FStar_Syntax_Util.unmeta t in
        let uu____1199 = FStar_Syntax_Util.head_and_args t1 in
        match uu____1199 with
        | (hd1,args) ->
            let uu____1240 =
              let uu____1253 =
                let uu____1254 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1254.FStar_Syntax_Syntax.n in
              (uu____1253, args) in
            (match uu____1240 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1270) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> FStar_Pervasives_Native.Some []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,_t::(hd2,uu____1292)::(tl1,uu____1294)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1341 = unembed_a hd2 in
                 FStar_Util.bind_opt uu____1341
                   (fun hd3  ->
                      let uu____1351 = __unembed_list w unembed_a tl1 in
                      FStar_Util.bind_opt uu____1351
                        (fun tl2  ->
                           FStar_Pervasives_Native.Some (hd3 :: tl2)))
             | uu____1370 ->
                 (if w
                  then
                    (let uu____1384 =
                       let uu____1385 = FStar_Syntax_Print.term_to_string t1 in
                       FStar_Util.format1 "Not an embedded list: %s"
                         uu____1385 in
                     FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____1384)
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
      let uu____1470 = embed_list embed_string FStar_Syntax_Syntax.t_string in
      uu____1470 rng ss
let unembed_string_list:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  = fun t  -> let uu____1488 = unembed_list unembed_string in uu____1488 t
let unembed_string_list_safe:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____1505 = unembed_list_safe unembed_string_safe in uu____1505 t
type norm_step =
  | Simpl
  | WHNF
  | Primops
  | Delta
  | Zeta
  | Iota
  | UnfoldOnly of Prims.string Prims.list[@@deriving show]
let uu___is_Simpl: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____1522 -> false
let uu___is_WHNF: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | WHNF  -> true | uu____1527 -> false
let uu___is_Primops: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1532 -> false
let uu___is_Delta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1537 -> false
let uu___is_Zeta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1542 -> false
let uu___is_Iota: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1547 -> false
let uu___is_UnfoldOnly: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____1555 -> false
let __proj__UnfoldOnly__item___0: norm_step -> Prims.string Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let steps_Simpl: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_simpl
let steps_WHNF: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_whnf
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
      | WHNF  -> steps_WHNF
      | Primops  -> steps_Primops
      | Delta  -> steps_Delta
      | Zeta  -> steps_Zeta
      | Iota  -> steps_Iota
      | UnfoldOnly l ->
          let uu____1584 =
            let uu____1585 =
              let uu____1586 =
                let uu____1587 =
                  let uu____1588 =
                    embed_list embed_string FStar_Syntax_Syntax.t_string in
                  uu____1588 rng l in
                FStar_Syntax_Syntax.as_arg uu____1587 in
              [uu____1586] in
            FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1585 in
          uu____1584 FStar_Pervasives_Native.None rng
let __unembed_norm_step:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option
  =
  fun w  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unascribe t in
      let uu____1611 = FStar_Syntax_Util.head_and_args t1 in
      match uu____1611 with
      | (hd1,args) ->
          let uu____1650 =
            let uu____1663 =
              let uu____1664 = FStar_Syntax_Util.un_uinst hd1 in
              uu____1664.FStar_Syntax_Syntax.n in
            (uu____1663, args) in
          (match uu____1650 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_simpl
               -> FStar_Pervasives_Native.Some Simpl
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_whnf
               -> FStar_Pervasives_Native.Some WHNF
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1769)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_unfoldonly
               ->
               let uu____1794 =
                 let uu____1799 = unembed_list unembed_string in uu____1799 l in
               FStar_Util.bind_opt uu____1794
                 (fun ss  ->
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                      (UnfoldOnly ss))
           | uu____1814 ->
               (if w
                then
                  (let uu____1828 =
                     let uu____1829 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded norm_step: %s"
                       uu____1829 in
                   FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____1828)
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
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
          FStar_Pervasives_Native.Some r
      | uu____1871 ->
          (if w
           then
             (let uu____1873 =
                let uu____1874 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded range: %s" uu____1874 in
              FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____1873)
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