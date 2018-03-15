open Prims
type 'a embedder = FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
[@@deriving show]
type 'a unembedder =
  FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option[@@deriving
                                                                 show]
let (embed_any :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun r -> fun t -> t
let (unembed_any :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun t -> FStar_Pervasives_Native.Some t
let (embed_unit :
  FStar_Range.range -> Prims.unit -> FStar_Syntax_Syntax.term) =
  fun rng ->
    fun u ->
      let uu___48_46 = FStar_Syntax_Util.exp_unit in
      {
        FStar_Syntax_Syntax.n = (uu___48_46.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___48_46.FStar_Syntax_Syntax.vars)
      }
let (__unembed_unit :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option)
  =
  fun w ->
    fun t0 ->
      let t = FStar_Syntax_Util.unascribe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) ->
          FStar_Pervasives_Native.Some ()
      | uu____62 ->
          (if w
           then
             (let uu____64 =
                let uu____69 =
                  let uu____70 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.format1 "Not an embedded unit: %s" uu____70 in
                (FStar_Errors.Warning_NotEmbedded, uu____69) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____64)
           else ();
           FStar_Pervasives_Native.None)
let (unembed_unit :
  FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option) =
  fun t -> __unembed_unit true t
let (unembed_unit_safe :
  FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option) =
  fun t -> __unembed_unit false t
let (embed_bool :
  FStar_Range.range -> Prims.bool -> FStar_Syntax_Syntax.term) =
  fun rng ->
    fun b ->
      let t =
        if b
        then FStar_Syntax_Util.exp_true_bool
        else FStar_Syntax_Util.exp_false_bool in
      let uu___49_101 = t in
      {
        FStar_Syntax_Syntax.n = (uu___49_101.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___49_101.FStar_Syntax_Syntax.vars)
      }
let (__unembed_bool :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option)
  =
  fun w ->
    fun t0 ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
          FStar_Pervasives_Native.Some b
      | uu____118 ->
          (if w
           then
             (let uu____120 =
                let uu____125 =
                  let uu____126 = FStar_Syntax_Print.term_to_string t0 in
                  FStar_Util.format1 "Not an embedded bool: %s" uu____126 in
                (FStar_Errors.Warning_NotEmbedded, uu____125) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____120)
           else ();
           FStar_Pervasives_Native.None)
let (unembed_bool :
  FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option) =
  fun t -> __unembed_bool true t
let (unembed_bool_safe :
  FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option) =
  fun t -> __unembed_bool false t
let (embed_char :
  FStar_Range.range -> FStar_Char.char -> FStar_Syntax_Syntax.term) =
  fun rng ->
    fun c ->
      let t = FStar_Syntax_Util.exp_char c in
      let uu___50_154 = t in
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
  fun w ->
    fun t0 ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
          FStar_Pervasives_Native.Some c
      | uu____172 ->
          (if w
           then
             (let uu____174 =
                let uu____179 =
                  let uu____180 = FStar_Syntax_Print.term_to_string t0 in
                  FStar_Util.format1 "Not an embedded char: %s" uu____180 in
                (FStar_Errors.Warning_NotEmbedded, uu____179) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____174)
           else ();
           FStar_Pervasives_Native.None)
let (unembed_char :
  FStar_Syntax_Syntax.term -> FStar_Char.char FStar_Pervasives_Native.option)
  = fun t -> __unembed_char true t
let (unembed_char_safe :
  FStar_Syntax_Syntax.term -> FStar_Char.char FStar_Pervasives_Native.option)
  = fun t -> __unembed_char false t
let (embed_int :
  FStar_Range.range -> FStar_BigInt.t -> FStar_Syntax_Syntax.term) =
  fun rng ->
    fun i ->
      let t =
        let uu____209 = FStar_BigInt.string_of_big_int i in
        FStar_Syntax_Util.exp_int uu____209 in
      let uu___51_210 = t in
      {
        FStar_Syntax_Syntax.n = (uu___51_210.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___51_210.FStar_Syntax_Syntax.vars)
      }
let (__unembed_int :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option)
  =
  fun w ->
    fun t0 ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
          (s, uu____225)) ->
          let uu____238 = FStar_BigInt.big_int_of_string s in
          FStar_Pervasives_Native.Some uu____238
      | uu____239 ->
          (if w
           then
             (let uu____241 =
                let uu____246 =
                  let uu____247 = FStar_Syntax_Print.term_to_string t0 in
                  FStar_Util.format1 "Not an embedded int: %s" uu____247 in
                (FStar_Errors.Warning_NotEmbedded, uu____246) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____241)
           else ();
           FStar_Pervasives_Native.None)
let (unembed_int :
  FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option)
  = fun t -> __unembed_int true t
let (unembed_int_safe :
  FStar_Syntax_Syntax.term -> FStar_BigInt.t FStar_Pervasives_Native.option)
  = fun t -> __unembed_int false t
let (embed_string :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term) =
  fun rng ->
    fun s ->
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
        FStar_Pervasives_Native.None rng
let (__unembed_string :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun w ->
    fun t0 ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
          (s, uu____286)) -> FStar_Pervasives_Native.Some s
      | uu____287 ->
          (if w
           then
             (let uu____289 =
                let uu____294 =
                  let uu____295 = FStar_Syntax_Print.term_to_string t0 in
                  FStar_Util.format1 "Not an embedded string: %s" uu____295 in
                (FStar_Errors.Warning_NotEmbedded, uu____294) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____289)
           else ();
           FStar_Pervasives_Native.None)
let (unembed_string :
  FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option) =
  fun t -> __unembed_string true t
let (unembed_string_safe :
  FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option) =
  fun t -> __unembed_string false t
let embed_pair :
  'a 'b .
    'a embedder ->
      FStar_Syntax_Syntax.typ ->
        'b embedder ->
          FStar_Syntax_Syntax.typ ->
            ('a, 'b) FStar_Pervasives_Native.tuple2 embedder
  =
  fun embed_a ->
    fun t_a ->
      fun embed_b ->
        fun t_b ->
          fun rng ->
            fun x ->
              let uu____378 =
                let uu____379 =
                  let uu____380 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.lid_Mktuple2 in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____380
                    [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
                let uu____381 =
                  let uu____382 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____383 =
                    let uu____386 = FStar_Syntax_Syntax.iarg t_b in
                    let uu____387 =
                      let uu____390 =
                        let uu____391 =
                          embed_a rng (FStar_Pervasives_Native.fst x) in
                        FStar_Syntax_Syntax.as_arg uu____391 in
                      let uu____395 =
                        let uu____398 =
                          let uu____399 =
                            embed_b rng (FStar_Pervasives_Native.snd x) in
                          FStar_Syntax_Syntax.as_arg uu____399 in
                        [uu____398] in
                      uu____390 :: uu____395 in
                    uu____386 :: uu____387 in
                  uu____382 :: uu____383 in
                FStar_Syntax_Syntax.mk_Tm_app uu____379 uu____381 in
              uu____378 FStar_Pervasives_Native.None rng
let __unembed_pair :
  'a 'b .
    Prims.bool ->
      'a unembedder ->
        'b unembedder ->
          FStar_Syntax_Syntax.term ->
            ('a, 'b) FStar_Pervasives_Native.tuple2
              FStar_Pervasives_Native.option
  =
  fun w ->
    fun unembed_a ->
      fun unembed_b ->
        fun t0 ->
          let t = FStar_Syntax_Util.unmeta_safe t0 in
          let uu____452 = FStar_Syntax_Util.head_and_args t in
          match uu____452 with
          | (hd1, args) ->
              let uu____495 =
                let uu____508 =
                  let uu____509 = FStar_Syntax_Util.un_uinst hd1 in
                  uu____509.FStar_Syntax_Syntax.n in
                (uu____508, args) in
              (match uu____495 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,
                  uu____527::uu____528::(a, uu____530)::(b, uu____532)::[])
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.lid_Mktuple2
                   ->
                   let uu____591 = unembed_a a in
                   FStar_Util.bind_opt uu____591
                     (fun a1 ->
                        let uu____603 = unembed_b b in
                        FStar_Util.bind_opt uu____603
                          (fun b1 -> FStar_Pervasives_Native.Some (a1, b1)))
               | uu____618 ->
                   (if w
                    then
                      (let uu____632 =
                         let uu____637 =
                           let uu____638 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1 "Not an embedded pair: %s"
                             uu____638 in
                         (FStar_Errors.Warning_NotEmbedded, uu____637) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____632)
                    else ();
                    FStar_Pervasives_Native.None))
let unembed_pair :
  'a 'b .
    'a unembedder ->
      'b unembedder -> ('a, 'b) FStar_Pervasives_Native.tuple2 unembedder
  = fun ul -> fun ur -> fun t -> __unembed_pair true ul ur t
let unembed_pair_safe :
  'a 'b .
    'a unembedder ->
      'b unembedder -> ('a, 'b) FStar_Pervasives_Native.tuple2 unembedder
  = fun ul -> fun ur -> fun t -> __unembed_pair false ul ur t
let embed_option :
  'a .
    'a embedder ->
      FStar_Syntax_Syntax.typ -> 'a FStar_Pervasives_Native.option embedder
  =
  fun embed_a ->
    fun typ ->
      fun rng ->
        fun o ->
          match o with
          | FStar_Pervasives_Native.None ->
              let uu____789 =
                let uu____790 =
                  let uu____791 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.none_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____791
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____792 =
                  let uu____793 = FStar_Syntax_Syntax.iarg typ in [uu____793] in
                FStar_Syntax_Syntax.mk_Tm_app uu____790 uu____792 in
              uu____789 FStar_Pervasives_Native.None rng
          | FStar_Pervasives_Native.Some a ->
              let uu____797 =
                let uu____798 =
                  let uu____799 =
                    FStar_Syntax_Syntax.tdataconstr
                      FStar_Parser_Const.some_lid in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____799
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____800 =
                  let uu____801 = FStar_Syntax_Syntax.iarg typ in
                  let uu____802 =
                    let uu____805 =
                      let uu____806 = embed_a rng a in
                      FStar_Syntax_Syntax.as_arg uu____806 in
                    [uu____805] in
                  uu____801 :: uu____802 in
                FStar_Syntax_Syntax.mk_Tm_app uu____798 uu____800 in
              uu____797 FStar_Pervasives_Native.None rng
let __unembed_option :
  'a .
    Prims.bool ->
      'a unembedder ->
        FStar_Syntax_Syntax.term ->
          'a FStar_Pervasives_Native.option FStar_Pervasives_Native.option
  =
  fun w ->
    fun unembed_a ->
      fun t0 ->
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        let uu____842 = FStar_Syntax_Util.head_and_args t in
        match uu____842 with
        | (hd1, args) ->
            let uu____883 =
              let uu____896 =
                let uu____897 = FStar_Syntax_Util.un_uinst hd1 in
                uu____897.FStar_Syntax_Syntax.n in
              (uu____896, args) in
            (match uu____883 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, uu____913) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
                 -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____933::(a, uu____935)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
                 ->
                 let uu____972 = unembed_a a in
                 FStar_Util.bind_opt uu____972
                   (fun a1 ->
                      FStar_Pervasives_Native.Some
                        (FStar_Pervasives_Native.Some a1))
             | uu____983 ->
                 (if w
                  then
                    (let uu____997 =
                       let uu____1002 =
                         let uu____1003 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1 "Not an embedded option: %s"
                           uu____1003 in
                       (FStar_Errors.Warning_NotEmbedded, uu____1002) in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____997)
                  else ();
                  FStar_Pervasives_Native.None))
let unembed_option :
  'a . 'a unembedder -> 'a FStar_Pervasives_Native.option unembedder =
  fun ua -> fun t -> __unembed_option true ua t
let unembed_option_safe :
  'a . 'a unembedder -> 'a FStar_Pervasives_Native.option unembedder =
  fun ua -> fun t -> __unembed_option false ua t
let embed_list :
  'a . 'a embedder -> FStar_Syntax_Syntax.typ -> 'a Prims.list embedder =
  fun embed_a ->
    fun typ ->
      fun rng ->
        fun l ->
          let t = FStar_Syntax_Syntax.iarg typ in
          let nil =
            let uu____1114 =
              let uu____1115 =
                let uu____1116 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____1116
                  [FStar_Syntax_Syntax.U_zero] in
              FStar_Syntax_Syntax.mk_Tm_app uu____1115 [t] in
            uu____1114 FStar_Pervasives_Native.None rng in
          let cons1 =
            let uu____1120 =
              FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____1120
              [FStar_Syntax_Syntax.U_zero] in
          FStar_List.fold_right
            (fun hd1 ->
               fun tail1 ->
                 let uu____1128 =
                   let uu____1129 =
                     let uu____1130 =
                       let uu____1133 =
                         let uu____1134 = embed_a rng hd1 in
                         FStar_Syntax_Syntax.as_arg uu____1134 in
                       let uu____1138 =
                         let uu____1141 = FStar_Syntax_Syntax.as_arg tail1 in
                         [uu____1141] in
                       uu____1133 :: uu____1138 in
                     t :: uu____1130 in
                   FStar_Syntax_Syntax.mk_Tm_app cons1 uu____1129 in
                 uu____1128 FStar_Pervasives_Native.None rng) l nil
let rec __unembed_list :
  'a .
    Prims.bool ->
      'a unembedder ->
        FStar_Syntax_Syntax.term ->
          'a Prims.list FStar_Pervasives_Native.option
  =
  fun w ->
    fun unembed_a ->
      fun t0 ->
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        let uu____1175 = FStar_Syntax_Util.head_and_args t in
        match uu____1175 with
        | (hd1, args) ->
            let uu____1216 =
              let uu____1229 =
                let uu____1230 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1230.FStar_Syntax_Syntax.n in
              (uu____1229, args) in
            (match uu____1216 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1246) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> FStar_Pervasives_Native.Some []
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                _t::(hd2, uu____1268)::(tl1, uu____1270)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1317 = unembed_a hd2 in
                 FStar_Util.bind_opt uu____1317
                   (fun hd3 ->
                      let uu____1327 = __unembed_list w unembed_a tl1 in
                      FStar_Util.bind_opt uu____1327
                        (fun tl2 -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
             | uu____1346 ->
                 (if w
                  then
                    (let uu____1360 =
                       let uu____1365 =
                         let uu____1366 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1 "Not an embedded list: %s"
                           uu____1366 in
                       (FStar_Errors.Warning_NotEmbedded, uu____1365) in
                     FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                       uu____1360)
                  else ();
                  FStar_Pervasives_Native.None))
let unembed_list : 'a . 'a unembedder -> 'a Prims.list unembedder =
  fun ua -> fun t -> __unembed_list true ua t
let unembed_list_safe : 'a . 'a unembedder -> 'a Prims.list unembedder =
  fun ua -> fun t -> __unembed_list false ua t
let embed_arrow_1 :
  'a 'b .
    'a unembedder ->
      'b embedder ->
        ('a -> 'b) ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ua ->
    fun eb ->
      fun f ->
        fun args ->
          match args with
          | (x, uu____1484)::[] ->
              let uu____1501 = ua x in
              FStar_Util.bind_opt uu____1501
                (fun a ->
                   let uu____1509 =
                     let uu____1510 =
                       let uu____1511 =
                         let uu____1512 = ua x in FStar_Util.must uu____1512 in
                       f uu____1511 in
                     eb FStar_Range.dummyRange uu____1510 in
                   FStar_Pervasives_Native.Some uu____1509)
          | uu____1520 -> FStar_Pervasives_Native.None
let embed_arrow_2 :
  'a 'b 'd .
    'a unembedder ->
      'b unembedder ->
        'd embedder ->
          ('a -> 'b -> 'd) ->
            FStar_Syntax_Syntax.args ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ua ->
    fun ub ->
      fun ed ->
        fun f ->
          fun args ->
            match args with
            | (x, uu____1593)::(y, uu____1595)::[] ->
                let uu____1622 = ua x in
                FStar_Util.bind_opt uu____1622
                  (fun a ->
                     let uu____1630 = ub y in
                     FStar_Util.bind_opt uu____1630
                       (fun b ->
                          let uu____1638 =
                            let uu____1639 = f a b in
                            ed FStar_Range.dummyRange uu____1639 in
                          FStar_Pervasives_Native.Some uu____1638))
            | uu____1643 -> FStar_Pervasives_Native.None
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
  fun ua ->
    fun ub ->
      fun uc ->
        fun ed ->
          fun f ->
            fun args ->
              match args with
              | (x, uu____1736)::(y, uu____1738)::(z, uu____1740)::[] ->
                  let uu____1777 = ua x in
                  FStar_Util.bind_opt uu____1777
                    (fun a ->
                       let uu____1785 = ub y in
                       FStar_Util.bind_opt uu____1785
                         (fun b ->
                            let uu____1793 = uc z in
                            FStar_Util.bind_opt uu____1793
                              (fun c ->
                                 let uu____1801 =
                                   let uu____1802 = f a b c in
                                   ed FStar_Range.dummyRange uu____1802 in
                                 FStar_Pervasives_Native.Some uu____1801)))
              | uu____1806 -> FStar_Pervasives_Native.None
let (embed_string_list :
  FStar_Range.range -> Prims.string Prims.list -> FStar_Syntax_Syntax.term) =
  fun rng ->
    fun ss ->
      let uu____1820 = embed_list embed_string FStar_Syntax_Syntax.t_string in
      uu____1820 rng ss
let (unembed_string_list :
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option)
  = fun t -> let uu____1837 = unembed_list unembed_string in uu____1837 t
let (unembed_string_list_safe :
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____1853 = unembed_list_safe unembed_string_safe in uu____1853 t
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
  fun projectee -> match projectee with | Simpl -> true | uu____1873 -> false
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____1877 -> false
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____1881 -> false
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | Primops -> true | uu____1885 -> false
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Delta -> true | uu____1889 -> false
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____1893 -> false
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____1897 -> false
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____1904 -> false
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____1922 -> false
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
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
  fun rng ->
    fun n1 ->
      match n1 with
      | Simpl -> steps_Simpl
      | Weak -> steps_Weak
      | HNF -> steps_HNF
      | Primops -> steps_Primops
      | Delta -> steps_Delta
      | Zeta -> steps_Zeta
      | Iota -> steps_Iota
      | UnfoldOnly l ->
          let uu____1942 =
            let uu____1943 =
              let uu____1944 =
                let uu____1945 =
                  let uu____1946 =
                    embed_list embed_string FStar_Syntax_Syntax.t_string in
                  uu____1946 rng l in
                FStar_Syntax_Syntax.as_arg uu____1945 in
              [uu____1944] in
            FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____1943 in
          uu____1942 FStar_Pervasives_Native.None rng
      | UnfoldAttr a ->
          let uu____1957 =
            let uu____1958 =
              let uu____1959 = FStar_Syntax_Syntax.as_arg a in [uu____1959] in
            FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____1958 in
          uu____1957 FStar_Pervasives_Native.None rng
let (__unembed_norm_step :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option)
  =
  fun w ->
    fun t0 ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      let uu____1973 = FStar_Syntax_Util.head_and_args t in
      match uu____1973 with
      | (hd1, args) ->
          let uu____2012 =
            let uu____2025 =
              let uu____2026 = FStar_Syntax_Util.un_uinst hd1 in
              uu____2026.FStar_Syntax_Syntax.n in
            (uu____2025, args) in
          (match uu____2012 with
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_simpl
               -> FStar_Pervasives_Native.Some Simpl
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak
               -> FStar_Pervasives_Native.Some Weak
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf
               -> FStar_Pervasives_Native.Some HNF
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_primops
               -> FStar_Pervasives_Native.Some Primops
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_delta
               -> FStar_Pervasives_Native.Some Delta
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta
               -> FStar_Pervasives_Native.Some Zeta
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota
               -> FStar_Pervasives_Native.Some Iota
           | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____2146)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_unfoldonly
               ->
               let uu____2171 =
                 let uu____2176 = unembed_list unembed_string in uu____2176 l in
               FStar_Util.bind_opt uu____2171
                 (fun ss ->
                    FStar_All.pipe_left
                      (fun _0_39 -> FStar_Pervasives_Native.Some _0_39)
                      (UnfoldOnly ss))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              uu____2192::(a, uu____2194)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.steps_unfoldattr
               -> FStar_Pervasives_Native.Some (UnfoldAttr a)
           | uu____2231 ->
               (if w
                then
                  (let uu____2245 =
                     let uu____2250 =
                       let uu____2251 = FStar_Syntax_Print.term_to_string t0 in
                       FStar_Util.format1 "Not an embedded norm_step: %s"
                         uu____2251 in
                     (FStar_Errors.Warning_NotEmbedded, uu____2250) in
                   FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                     uu____2245)
                else ();
                FStar_Pervasives_Native.None))
let (unembed_norm_step :
  FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option) =
  fun t -> __unembed_norm_step true t
let (unembed_norm_step_safe :
  FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option) =
  fun t -> __unembed_norm_step false t
let (embed_range :
  FStar_Range.range -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun rng ->
    fun r ->
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
        FStar_Pervasives_Native.None rng
let (__unembed_range :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Range.range FStar_Pervasives_Native.option)
  =
  fun w ->
    fun t0 ->
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
          FStar_Pervasives_Native.Some r
      | uu____2290 ->
          (if w
           then
             (let uu____2292 =
                let uu____2297 =
                  let uu____2298 = FStar_Syntax_Print.term_to_string t0 in
                  FStar_Util.format1 "Not an embedded range: %s" uu____2298 in
                (FStar_Errors.Warning_NotEmbedded, uu____2297) in
              FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2292)
           else ();
           FStar_Pervasives_Native.None)
let (unembed_range :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range FStar_Pervasives_Native.option)
  = fun t -> __unembed_range true t
let (unembed_range_safe :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range FStar_Pervasives_Native.option)
  = fun t -> __unembed_range false t