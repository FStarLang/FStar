open Prims
let (embed_unit :Prims.unit -> FStar_Syntax_Syntax.term)=
  fun u  -> FStar_Syntax_Util.exp_unit
let (unembed_unit :FStar_Syntax_Syntax.term -> Prims.unit)=
  fun uu____8  -> ()
let (embed_bool :Prims.bool -> FStar_Syntax_Syntax.term)=
  fun b  ->
    if b
    then FStar_Syntax_Util.exp_true_bool
    else FStar_Syntax_Util.exp_false_bool
let (unembed_bool :FStar_Syntax_Syntax.term -> Prims.bool)=
  fun t  ->
    let uu____18 =
      let uu____19 =
        let uu____22 = FStar_Syntax_Util.unmeta t in
        FStar_Syntax_Subst.compress uu____22 in
      uu____19.FStar_Syntax_Syntax.n in
    match uu____18 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____24 -> failwith "Not an embedded bool"
let (embed_int :Prims.int -> FStar_Syntax_Syntax.term)=
  fun i  ->
    let uu____29 = FStar_Util.string_of_int i in
    FStar_Syntax_Util.exp_int uu____29
let (unembed_int :FStar_Syntax_Syntax.term -> Prims.int)=
  fun t  ->
    let uu____34 =
      let uu____35 =
        let uu____38 = FStar_Syntax_Util.unmeta t in
        FStar_Syntax_Subst.compress uu____38 in
      uu____35.FStar_Syntax_Syntax.n in
    match uu____34 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____40)) ->
        FStar_Util.int_of_string s
    | uu____53 -> failwith "Not an embedded int"
let (embed_string :Prims.string -> FStar_Syntax_Syntax.term)=
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s in
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (bytes, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
let (unembed_string :FStar_Syntax_Syntax.term -> Prims.string)=
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____69)) -> FStar_Util.string_of_unicode bytes
    | uu____74 ->
        let uu____75 =
          let uu____76 =
            let uu____77 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____77 ")" in
          Prims.strcat "Not an embedded string (" uu____76 in
        failwith uu____75
let embed_pair :
  'a 'b .
    ('a -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term ->
        ('b -> FStar_Syntax_Syntax.term) ->
          FStar_Syntax_Syntax.term ->
            ('a,'b) FStar_Pervasives_Native.tuple2 ->
              FStar_Syntax_Syntax.term=
  fun embed_a  ->
    fun t_a  ->
      fun embed_b  ->
        fun t_b  ->
          fun x  ->
            let uu____132 =
              let uu____133 =
                let uu____134 =
                  FStar_Syntax_Syntax.tdataconstr
                    FStar_Parser_Const.lid_Mktuple2 in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____134
                  [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
              let uu____135 =
                let uu____136 = FStar_Syntax_Syntax.iarg t_a in
                let uu____137 =
                  let uu____140 = FStar_Syntax_Syntax.iarg t_b in
                  let uu____141 =
                    let uu____144 =
                      let uu____145 = embed_a (FStar_Pervasives_Native.fst x) in
                      FStar_Syntax_Syntax.as_arg uu____145 in
                    let uu____146 =
                      let uu____149 =
                        let uu____150 =
                          embed_b (FStar_Pervasives_Native.snd x) in
                        FStar_Syntax_Syntax.as_arg uu____150 in
                      [uu____149] in
                    uu____144 :: uu____146 in
                  uu____140 :: uu____141 in
                uu____136 :: uu____137 in
              FStar_Syntax_Syntax.mk_Tm_app uu____133 uu____135 in
            uu____132 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_pair :
  'a 'b .
    (FStar_Syntax_Syntax.term -> 'a) ->
      (FStar_Syntax_Syntax.term -> 'b) ->
        FStar_Syntax_Syntax.term -> ('a,'b) FStar_Pervasives_Native.tuple2=
  fun unembed_a  ->
    fun unembed_b  ->
      fun pair  ->
        let pairs = FStar_Syntax_Util.unmeta pair in
        let uu____192 = FStar_Syntax_Util.head_and_args pair in
        match uu____192 with
        | (hd1,args) ->
            let uu____233 =
              let uu____246 =
                let uu____247 = FStar_Syntax_Util.un_uinst hd1 in
                uu____247.FStar_Syntax_Syntax.n in
              (uu____246, args) in
            (match uu____233 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____263::uu____264::(a,uu____266)::(b,uu____268)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____327 = unembed_a a in
                 let uu____328 = unembed_b b in (uu____327, uu____328)
             | uu____329 -> failwith "Not an embedded pair")
let embed_option :
  'a .
    ('a -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term ->
        'a FStar_Pervasives_Native.option -> FStar_Syntax_Syntax.term=
  fun embed_a  ->
    fun typ  ->
      fun o  ->
        match o with
        | FStar_Pervasives_Native.None  ->
            let uu____376 =
              let uu____377 =
                let uu____378 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____378
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____379 =
                let uu____380 = FStar_Syntax_Syntax.iarg typ in [uu____380] in
              FStar_Syntax_Syntax.mk_Tm_app uu____377 uu____379 in
            uu____376 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Pervasives_Native.Some a ->
            let uu____384 =
              let uu____385 =
                let uu____386 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____386
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____387 =
                let uu____388 = FStar_Syntax_Syntax.iarg typ in
                let uu____389 =
                  let uu____392 =
                    let uu____393 = embed_a a in
                    FStar_Syntax_Syntax.as_arg uu____393 in
                  [uu____392] in
                uu____388 :: uu____389 in
              FStar_Syntax_Syntax.mk_Tm_app uu____385 uu____387 in
            uu____384 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_option :
  'a .
    (FStar_Syntax_Syntax.term -> 'a) ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option=
  fun unembed_a  ->
    fun o  ->
      let uu____418 =
        let uu____433 = FStar_Syntax_Util.unmeta o in
        FStar_Syntax_Util.head_and_args uu____433 in
      match uu____418 with
      | (hd1,args) ->
          let uu____458 =
            let uu____471 =
              let uu____472 = FStar_Syntax_Util.un_uinst hd1 in
              uu____472.FStar_Syntax_Syntax.n in
            (uu____471, args) in
          (match uu____458 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____486) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____504::(a,uu____506)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____543 = unembed_a a in
               FStar_Pervasives_Native.Some uu____543
           | uu____544 -> failwith "Not an embedded option")
let rec embed_list :
  'a .
    ('a -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term -> 'a Prims.list -> FStar_Syntax_Syntax.term=
  fun embed_a  ->
    fun typ  ->
      fun l  ->
        match l with
        | [] ->
            let uu____590 =
              let uu____591 =
                let uu____592 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____592
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____593 =
                let uu____594 = FStar_Syntax_Syntax.iarg typ in [uu____594] in
              FStar_Syntax_Syntax.mk_Tm_app uu____591 uu____593 in
            uu____590 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | hd1::tl1 ->
            let uu____601 =
              let uu____602 =
                let uu____603 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____603
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____604 =
                let uu____605 = FStar_Syntax_Syntax.iarg typ in
                let uu____606 =
                  let uu____609 =
                    let uu____610 = embed_a hd1 in
                    FStar_Syntax_Syntax.as_arg uu____610 in
                  let uu____611 =
                    let uu____614 =
                      let uu____615 = embed_list embed_a typ tl1 in
                      FStar_Syntax_Syntax.as_arg uu____615 in
                    [uu____614] in
                  uu____609 :: uu____611 in
                uu____605 :: uu____606 in
              FStar_Syntax_Syntax.mk_Tm_app uu____602 uu____604 in
            uu____601 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_list :
  'a .
    (FStar_Syntax_Syntax.term -> 'a) ->
      FStar_Syntax_Syntax.term -> 'a Prims.list=
  fun unembed_a  ->
    fun l  ->
      let l1 = FStar_Syntax_Util.unmeta l in
      let uu____642 = FStar_Syntax_Util.head_and_args l1 in
      match uu____642 with
      | (hd1,args) ->
          let uu____681 =
            let uu____694 =
              let uu____695 = FStar_Syntax_Util.un_uinst hd1 in
              uu____695.FStar_Syntax_Syntax.n in
            (uu____694, args) in
          (match uu____681 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____709) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,_t::(hd2,uu____729)::(tl1,uu____731)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____778 = unembed_a hd2 in
               let uu____779 = unembed_list unembed_a tl1 in uu____778 ::
                 uu____779
           | uu____782 ->
               let uu____795 =
                 let uu____796 = FStar_Syntax_Print.tag_of_term l1 in
                 let uu____797 = FStar_Syntax_Print.term_to_string l1 in
                 FStar_Util.format2 "(%s) Not an embedded list: %s" uu____796
                   uu____797 in
               failwith uu____795)
let (embed_string_list :Prims.string Prims.list -> FStar_Syntax_Syntax.term)=
  fun ss  -> embed_list embed_string FStar_Syntax_Syntax.t_string ss
let (unembed_string_list
  :FStar_Syntax_Syntax.term -> Prims.string Prims.list)=
  fun t  -> unembed_list unembed_string t