open Prims
let embed_unit: Prims.unit -> FStar_Syntax_Syntax.term =
  fun u  -> FStar_Syntax_Util.exp_unit
let unembed_unit:
  FStar_Syntax_Syntax.term -> Prims.unit FStar_Pervasives_Native.option =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____16 -> FStar_Pervasives_Native.None
let embed_bool: Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Util.exp_true_bool
    else FStar_Syntax_Util.exp_false_bool
let unembed_bool:
  FStar_Syntax_Syntax.term -> Prims.bool FStar_Pervasives_Native.option =
  fun t  ->
    let uu____30 =
      let uu____31 =
        let uu____34 = FStar_Syntax_Util.unmeta t in
        FStar_Syntax_Subst.compress uu____34 in
      uu____31.FStar_Syntax_Syntax.n in
    match uu____30 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____38 ->
        ((let uu____40 =
            let uu____41 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded bool: %s" uu____41 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____40);
         FStar_Pervasives_Native.None)
let embed_int: Prims.int -> FStar_Syntax_Syntax.term =
  fun i  ->
    let uu____46 = FStar_Util.string_of_int i in
    FStar_Syntax_Util.exp_int uu____46
let unembed_int:
  FStar_Syntax_Syntax.term -> Prims.int FStar_Pervasives_Native.option =
  fun t  ->
    let uu____55 =
      let uu____56 =
        let uu____59 = FStar_Syntax_Util.unmeta t in
        FStar_Syntax_Subst.compress uu____59 in
      uu____56.FStar_Syntax_Syntax.n in
    match uu____55 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____63)) ->
        let uu____76 = FStar_Util.int_of_string s in
        FStar_Pervasives_Native.Some uu____76
    | uu____77 ->
        ((let uu____79 =
            let uu____80 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded int: %s" uu____80 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____79);
         FStar_Pervasives_Native.None)
let embed_string: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_string:
  FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s,uu____97))
        -> FStar_Pervasives_Native.Some s
    | uu____98 ->
        ((let uu____100 =
            let uu____101 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Not an embedded string: %s" uu____101 in
          FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____100);
         FStar_Pervasives_Native.None)
let embed_pair:
  'a 'b .
    ('a -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term ->
        ('b -> FStar_Syntax_Syntax.term) ->
          FStar_Syntax_Syntax.term ->
            ('a,'b) FStar_Pervasives_Native.tuple2 ->
              FStar_Syntax_Syntax.term
  =
  fun embed_a  ->
    fun t_a  ->
      fun embed_b  ->
        fun t_b  ->
          fun x  ->
            let uu____156 =
              let uu____157 =
                let uu____158 =
                  FStar_Syntax_Syntax.tdataconstr
                    FStar_Parser_Const.lid_Mktuple2 in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____158
                  [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
              let uu____159 =
                let uu____160 = FStar_Syntax_Syntax.iarg t_a in
                let uu____161 =
                  let uu____164 = FStar_Syntax_Syntax.iarg t_b in
                  let uu____165 =
                    let uu____168 =
                      let uu____169 = embed_a (FStar_Pervasives_Native.fst x) in
                      FStar_Syntax_Syntax.as_arg uu____169 in
                    let uu____170 =
                      let uu____173 =
                        let uu____174 =
                          embed_b (FStar_Pervasives_Native.snd x) in
                        FStar_Syntax_Syntax.as_arg uu____174 in
                      [uu____173] in
                    uu____168 :: uu____170 in
                  uu____164 :: uu____165 in
                uu____160 :: uu____161 in
              FStar_Syntax_Syntax.mk_Tm_app uu____157 uu____159 in
            uu____156 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_pair:
  'a 'b .
    (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.term -> 'b FStar_Pervasives_Native.option) ->
        FStar_Syntax_Syntax.term ->
          ('a,'b) FStar_Pervasives_Native.tuple2
            FStar_Pervasives_Native.option
  =
  fun unembed_a  ->
    fun unembed_b  ->
      fun t  ->
        let t1 = FStar_Syntax_Util.unmeta t in
        let uu____226 = FStar_Syntax_Util.head_and_args t1 in
        match uu____226 with
        | (hd1,args) ->
            let uu____269 =
              let uu____282 =
                let uu____283 = FStar_Syntax_Util.un_uinst hd1 in
                uu____283.FStar_Syntax_Syntax.n in
              (uu____282, args) in
            (match uu____269 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____301::uu____302::(a,uu____304)::(b,uu____306)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____365 = unembed_a a in
                 FStar_Util.bind_opt uu____365
                   (fun a1  ->
                      let uu____375 = unembed_b b in
                      FStar_Util.bind_opt uu____375
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____388 ->
                 ((let uu____402 =
                     let uu____403 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded pair: %s" uu____403 in
                   FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____402);
                  FStar_Pervasives_Native.None))
let embed_option:
  'a .
    ('a -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term ->
        'a FStar_Pervasives_Native.option -> FStar_Syntax_Syntax.term
  =
  fun embed_a  ->
    fun typ  ->
      fun o  ->
        match o with
        | FStar_Pervasives_Native.None  ->
            let uu____438 =
              let uu____439 =
                let uu____440 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____440
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____441 =
                let uu____442 = FStar_Syntax_Syntax.iarg typ in [uu____442] in
              FStar_Syntax_Syntax.mk_Tm_app uu____439 uu____441 in
            uu____438 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Pervasives_Native.Some a ->
            let uu____446 =
              let uu____447 =
                let uu____448 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____448
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____449 =
                let uu____450 = FStar_Syntax_Syntax.iarg typ in
                let uu____451 =
                  let uu____454 =
                    let uu____455 = embed_a a in
                    FStar_Syntax_Syntax.as_arg uu____455 in
                  [uu____454] in
                uu____450 :: uu____451 in
              FStar_Syntax_Syntax.mk_Tm_app uu____447 uu____449 in
            uu____446 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_option:
  'a .
    (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term ->
        'a FStar_Pervasives_Native.option FStar_Pervasives_Native.option
  =
  fun unembed_a  ->
    fun t  ->
      let uu____486 =
        let uu____501 = FStar_Syntax_Util.unmeta t in
        FStar_Syntax_Util.head_and_args uu____501 in
      match uu____486 with
      | (hd1,args) ->
          let uu____528 =
            let uu____541 =
              let uu____542 = FStar_Syntax_Util.un_uinst hd1 in
              uu____542.FStar_Syntax_Syntax.n in
            (uu____541, args) in
          (match uu____528 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____558) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____578::(a,uu____580)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____617 = unembed_a a in
               FStar_Util.bind_opt uu____617
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____626 ->
               ((let uu____640 =
                   let uu____641 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.format1 "Not an embedded option: %s" uu____641 in
                 FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____640);
                FStar_Pervasives_Native.None))
let rec embed_list:
  'a .
    ('a -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term -> 'a Prims.list -> FStar_Syntax_Syntax.term
  =
  fun embed_a  ->
    fun typ  ->
      fun l  ->
        match l with
        | [] ->
            let uu____674 =
              let uu____675 =
                let uu____676 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____676
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____677 =
                let uu____678 = FStar_Syntax_Syntax.iarg typ in [uu____678] in
              FStar_Syntax_Syntax.mk_Tm_app uu____675 uu____677 in
            uu____674 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | hd1::tl1 ->
            let uu____685 =
              let uu____686 =
                let uu____687 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____687
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____688 =
                let uu____689 = FStar_Syntax_Syntax.iarg typ in
                let uu____690 =
                  let uu____693 =
                    let uu____694 = embed_a hd1 in
                    FStar_Syntax_Syntax.as_arg uu____694 in
                  let uu____695 =
                    let uu____698 =
                      let uu____699 = embed_list embed_a typ tl1 in
                      FStar_Syntax_Syntax.as_arg uu____699 in
                    [uu____698] in
                  uu____693 :: uu____695 in
                uu____689 :: uu____690 in
              FStar_Syntax_Syntax.mk_Tm_app uu____686 uu____688 in
            uu____685 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_list:
  'a .
    (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term ->
        'a Prims.list FStar_Pervasives_Native.option
  =
  fun unembed_a  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____731 = FStar_Syntax_Util.head_and_args t1 in
      match uu____731 with
      | (hd1,args) ->
          let uu____772 =
            let uu____785 =
              let uu____786 = FStar_Syntax_Util.un_uinst hd1 in
              uu____786.FStar_Syntax_Syntax.n in
            (uu____785, args) in
          (match uu____772 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____802) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,_t::(hd2,uu____824)::(tl1,uu____826)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____873 = unembed_a hd2 in
               FStar_Util.bind_opt uu____873
                 (fun hd3  ->
                    let uu____881 = unembed_list unembed_a tl1 in
                    FStar_Util.bind_opt uu____881
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd3 :: tl2)))
           | uu____896 ->
               ((let uu____910 =
                   let uu____911 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.format1 "Not an embedded list: %s" uu____911 in
                 FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____910);
                FStar_Pervasives_Native.None))
let embed_string_list: Prims.string Prims.list -> FStar_Syntax_Syntax.term =
  fun ss  -> embed_list embed_string FStar_Syntax_Syntax.t_string ss
let unembed_string_list:
  FStar_Syntax_Syntax.term ->
    Prims.string Prims.list FStar_Pervasives_Native.option
  = fun t  -> unembed_list unembed_string t
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
    match projectee with | Simpl  -> true | uu____940 -> false
let uu___is_WHNF: norm_step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____945 -> false
let uu___is_Primops: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____950 -> false
let uu___is_Delta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____955 -> false
let uu___is_Zeta: norm_step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____960 -> false
let uu___is_Iota: norm_step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____965 -> false
let uu___is_UnfoldOnly: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____973 -> false
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
let embed_norm_step: norm_step -> FStar_Syntax_Syntax.term =
  fun n1  ->
    match n1 with
    | Simpl  -> steps_Simpl
    | WHNF  -> steps_WHNF
    | Primops  -> steps_Primops
    | Delta  -> steps_Delta
    | Zeta  -> steps_Zeta
    | Iota  -> steps_Iota
    | UnfoldOnly l ->
        let uu____995 =
          let uu____996 =
            let uu____997 =
              let uu____998 =
                embed_list embed_string FStar_Syntax_Syntax.t_string l in
              FStar_Syntax_Syntax.as_arg uu____998 in
            [uu____997] in
          FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____996 in
        uu____995 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_norm_step:
  FStar_Syntax_Syntax.term -> norm_step FStar_Pervasives_Native.option =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1010 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1010 with
    | (hd1,args) ->
        let uu____1049 =
          let uu____1062 =
            let uu____1063 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1063.FStar_Syntax_Syntax.n in
          (uu____1062, args) in
        (match uu____1049 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl
             -> FStar_Pervasives_Native.Some Simpl
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_whnf
             -> FStar_Pervasives_Native.Some WHNF
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____1168)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.steps_unfoldonly
             ->
             let uu____1193 = unembed_list unembed_string l in
             FStar_Util.bind_opt uu____1193
               (fun ss  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (UnfoldOnly ss))
         | uu____1206 ->
             ((let uu____1220 =
                 let uu____1221 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded norm_step: %s"
                   uu____1221 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____1220);
              FStar_Pervasives_Native.None))
let embed_range: FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun r  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
let unembed_range:
  FStar_Syntax_Syntax.term ->
    FStar_Range.range FStar_Pervasives_Native.option
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu____1235 ->
        ((let uu____1237 =
            let uu____1238 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded range: %s" uu____1238 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____1237);
         FStar_Pervasives_Native.None)