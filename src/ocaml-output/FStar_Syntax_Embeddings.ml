open Prims
let embed_unit: Prims.unit -> FStar_Syntax_Syntax.term =
  fun u  -> FStar_Syntax_Util.exp_unit
let unembed_unit: FStar_Syntax_Syntax.term -> Prims.unit = fun uu____8  -> ()
let embed_bool: Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Util.exp_true_bool
    else FStar_Syntax_Util.exp_false_bool
let unembed_bool: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____18 =
      let uu____19 = FStar_Syntax_Subst.compress t in
      uu____19.FStar_Syntax_Syntax.n in
    match uu____18 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____23 -> failwith "Not an embedded bool"
let embed_int: Prims.int -> FStar_Syntax_Syntax.term =
  fun i  ->
    let uu____28 = FStar_Util.string_of_int i in
    FStar_Syntax_Util.exp_int uu____28
let unembed_int: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____33 =
      let uu____34 = FStar_Syntax_Subst.compress t in
      uu____34.FStar_Syntax_Syntax.n in
    match uu____33 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____38)) ->
        FStar_Util.int_of_string s
    | uu____51 -> failwith "Not an embedded int"
let embed_string: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s in
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (bytes, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____67)) -> FStar_Util.string_of_unicode bytes
    | uu____72 ->
        let uu____73 =
          let uu____74 =
            let uu____75 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____75 ")" in
          Prims.strcat "Not an embedded string (" uu____74 in
        failwith uu____73
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
            let uu____130 =
              let uu____131 =
                let uu____132 =
                  FStar_Syntax_Syntax.tdataconstr
                    FStar_Parser_Const.lid_Mktuple2 in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____132
                  [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
              let uu____133 =
                let uu____134 = FStar_Syntax_Syntax.iarg t_a in
                let uu____135 =
                  let uu____138 = FStar_Syntax_Syntax.iarg t_b in
                  let uu____139 =
                    let uu____142 =
                      let uu____143 = embed_a (FStar_Pervasives_Native.fst x) in
                      FStar_Syntax_Syntax.as_arg uu____143 in
                    let uu____144 =
                      let uu____147 =
                        let uu____148 =
                          embed_b (FStar_Pervasives_Native.snd x) in
                        FStar_Syntax_Syntax.as_arg uu____148 in
                      [uu____147] in
                    uu____142 :: uu____144 in
                  uu____138 :: uu____139 in
                uu____134 :: uu____135 in
              FStar_Syntax_Syntax.mk_Tm_app uu____131 uu____133 in
            uu____130 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_pair:
  'a 'b .
    (FStar_Syntax_Syntax.term -> 'a) ->
      (FStar_Syntax_Syntax.term -> 'b) ->
        FStar_Syntax_Syntax.term -> ('a,'b) FStar_Pervasives_Native.tuple2
  =
  fun unembed_a  ->
    fun unembed_b  ->
      fun pair  ->
        let pairs = FStar_Syntax_Util.unascribe pair in
        let uu____190 = FStar_Syntax_Util.head_and_args pair in
        match uu____190 with
        | (hd1,args) ->
            let uu____231 =
              let uu____244 =
                let uu____245 = FStar_Syntax_Util.un_uinst hd1 in
                uu____245.FStar_Syntax_Syntax.n in
              (uu____244, args) in
            (match uu____231 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____261::uu____262::(a,uu____264)::(b,uu____266)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____325 = unembed_a a in
                 let uu____326 = unembed_b b in (uu____325, uu____326)
             | uu____327 -> failwith "Not an embedded pair")
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
            let uu____374 =
              let uu____375 =
                let uu____376 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____376
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____377 =
                let uu____378 = FStar_Syntax_Syntax.iarg typ in [uu____378] in
              FStar_Syntax_Syntax.mk_Tm_app uu____375 uu____377 in
            uu____374 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Pervasives_Native.Some a ->
            let uu____382 =
              let uu____383 =
                let uu____384 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____384
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____385 =
                let uu____386 = FStar_Syntax_Syntax.iarg typ in
                let uu____387 =
                  let uu____390 =
                    let uu____391 = embed_a a in
                    FStar_Syntax_Syntax.as_arg uu____391 in
                  [uu____390] in
                uu____386 :: uu____387 in
              FStar_Syntax_Syntax.mk_Tm_app uu____383 uu____385 in
            uu____382 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_option:
  'a .
    (FStar_Syntax_Syntax.term -> 'a) ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun unembed_a  ->
    fun o  ->
      let uu____416 = FStar_Syntax_Util.head_and_args o in
      match uu____416 with
      | (hd1,args) ->
          let uu____455 =
            let uu____468 =
              let uu____469 = FStar_Syntax_Util.un_uinst hd1 in
              uu____469.FStar_Syntax_Syntax.n in
            (uu____468, args) in
          (match uu____455 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____483) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____501::(a,uu____503)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____540 = unembed_a a in
               FStar_Pervasives_Native.Some uu____540
           | uu____541 -> failwith "Not an embedded option")
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
            let uu____586 =
              let uu____587 =
                let uu____588 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____588
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____589 =
                let uu____590 = FStar_Syntax_Syntax.iarg typ in [uu____590] in
              FStar_Syntax_Syntax.mk_Tm_app uu____587 uu____589 in
            uu____586 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | hd1::tl1 ->
            let uu____597 =
              let uu____598 =
                let uu____599 =
                  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____599
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____600 =
                let uu____601 = FStar_Syntax_Syntax.iarg typ in
                let uu____602 =
                  let uu____605 =
                    let uu____606 = embed_a hd1 in
                    FStar_Syntax_Syntax.as_arg uu____606 in
                  let uu____607 =
                    let uu____610 =
                      let uu____611 = embed_list embed_a typ tl1 in
                      FStar_Syntax_Syntax.as_arg uu____611 in
                    [uu____610] in
                  uu____605 :: uu____607 in
                uu____601 :: uu____602 in
              FStar_Syntax_Syntax.mk_Tm_app uu____598 uu____600 in
            uu____597 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_list:
  'a .
    (FStar_Syntax_Syntax.term -> 'a) ->
      FStar_Syntax_Syntax.term -> 'a Prims.list
  =
  fun unembed_a  ->
    fun l  ->
      let l1 = FStar_Syntax_Util.unascribe l in
      let uu____637 = FStar_Syntax_Util.head_and_args l1 in
      match uu____637 with
      | (hd1,args) ->
          let uu____676 =
            let uu____689 =
              let uu____690 = FStar_Syntax_Util.un_uinst hd1 in
              uu____690.FStar_Syntax_Syntax.n in
            (uu____689, args) in
          (match uu____676 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____704) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,_t::(hd2,uu____724)::(tl1,uu____726)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____773 = unembed_a hd2 in
               let uu____774 = unembed_list unembed_a tl1 in uu____773 ::
                 uu____774
           | uu____777 ->
               let uu____790 =
                 let uu____791 = FStar_Syntax_Print.term_to_string l1 in
                 FStar_Util.format1 "Not an embedded list: %s" uu____791 in
               failwith uu____790)
let embed_string_list: Prims.string Prims.list -> FStar_Syntax_Syntax.term =
  fun ss  -> embed_list embed_string FStar_Syntax_Syntax.t_string ss
let unembed_string_list: FStar_Syntax_Syntax.term -> Prims.string Prims.list
  = fun t  -> unembed_list unembed_string t