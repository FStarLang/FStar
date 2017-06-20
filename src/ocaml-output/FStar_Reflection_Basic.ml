open Prims
let protect_embedded_term:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____11 =
        let uu____12 =
          let uu____13 = FStar_Syntax_Syntax.iarg t in
          let uu____14 =
            let uu____16 = FStar_Syntax_Syntax.as_arg x in [uu____16] in
          uu____13 :: uu____14 in
        FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Const.fstar_refl_embed
          uu____12 in
      uu____11 None x.FStar_Syntax_Syntax.pos
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____25 = FStar_Syntax_Util.head_and_args t in
    match uu____25 with
    | (head1,args) ->
        let uu____51 =
          let uu____59 =
            let uu____60 = FStar_Syntax_Util.un_uinst head1 in
            uu____60.FStar_Syntax_Syntax.n in
          (uu____59, args) in
        (match uu____51 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____69::(x,uu____71)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Syntax_Const.fstar_refl_embed_lid
             -> x
         | uu____97 ->
             let uu____105 =
               let uu____106 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____106 in
             failwith uu____105)
let embed_unit: Prims.unit -> FStar_Syntax_Syntax.term =
  fun u  -> FStar_Syntax_Const.exp_unit
let unembed_unit: FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____114  -> ()
let embed_bool: Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Const.exp_true_bool
    else FStar_Syntax_Const.exp_false_bool
let unembed_bool: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____124 =
      let uu____125 = FStar_Syntax_Subst.compress t in
      uu____125.FStar_Syntax_Syntax.n in
    match uu____124 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____129 -> failwith "Not an embedded bool"
let embed_int: Prims.int -> FStar_Syntax_Syntax.term =
  fun i  ->
    let uu____134 = FStar_Util.string_of_int i in
    FStar_Syntax_Const.exp_int uu____134
let unembed_int: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____139 =
      let uu____140 = FStar_Syntax_Subst.compress t in
      uu____140.FStar_Syntax_Syntax.n in
    match uu____139 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____144))
        -> FStar_Util.int_of_string s
    | uu____151 -> failwith "Not an embedded int"
let embed_string:
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s in
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (bytes, FStar_Range.dummyRange))) None
      FStar_Range.dummyRange
let unembed_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____169)) -> FStar_Util.string_of_unicode bytes
    | uu____172 ->
        let uu____173 =
          let uu____174 =
            let uu____175 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____175 ")" in
          Prims.strcat "Not an embedded string (" uu____174 in
        failwith uu____173
let lid_Mktuple2: FStar_Ident.lident =
  FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2")
    FStar_Range.dummyRange
let lid_tuple2: FStar_Ident.lident =
  FStar_Syntax_Util.mk_tuple_lid (Prims.parse_int "2") FStar_Range.dummyRange
let embed_binder: FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term =
  fun b  -> FStar_Syntax_Util.mk_alien b "reflection.embed_binder" None
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let uu____184 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____184 FStar_Dyn.undyn
let rec embed_list embed_a typ l =
  match l with
  | [] ->
      let uu____213 =
        let uu____214 =
          let uu____215 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____215
            [FStar_Syntax_Syntax.U_zero] in
        let uu____216 =
          let uu____217 = FStar_Syntax_Syntax.iarg typ in [uu____217] in
        FStar_Syntax_Syntax.mk_Tm_app uu____214 uu____216 in
      uu____213 None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____225 =
        let uu____226 =
          let uu____227 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____227
            [FStar_Syntax_Syntax.U_zero] in
        let uu____228 =
          let uu____229 = FStar_Syntax_Syntax.iarg typ in
          let uu____230 =
            let uu____232 =
              let uu____233 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____233 in
            let uu____234 =
              let uu____236 =
                let uu____237 = embed_list embed_a typ tl1 in
                FStar_Syntax_Syntax.as_arg uu____237 in
              [uu____236] in
            uu____232 :: uu____234 in
          uu____229 :: uu____230 in
        FStar_Syntax_Syntax.mk_Tm_app uu____226 uu____228 in
      uu____225 None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____264 = FStar_Syntax_Util.head_and_args l1 in
  match uu____264 with
  | (hd1,args) ->
      let uu____291 =
        let uu____299 =
          let uu____300 = FStar_Syntax_Util.un_uinst hd1 in
          uu____300.FStar_Syntax_Syntax.n in
        (uu____299, args) in
      (match uu____291 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____310) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____324)::(tl1,uu____326)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
           let uu____360 = unembed_a hd2 in
           let uu____361 = unembed_list unembed_a tl1 in uu____360 ::
             uu____361
       | uu____363 ->
           let uu____371 =
             let uu____372 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____372 in
           failwith uu____371)
let embed_binders:
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list embed_binder FStar_Reflection_Data.fstar_refl_binder l
let unembed_binders:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder Prims.list =
  fun t  -> unembed_list unembed_binder t
let embed_term:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> protect_embedded_term FStar_Reflection_Data.fstar_refl_term t
let unembed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t
let embed_pair embed_a t_a embed_b t_b x =
  let uu____443 =
    let uu____444 =
      let uu____445 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____445
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____446 =
      let uu____447 = FStar_Syntax_Syntax.iarg t_a in
      let uu____448 =
        let uu____450 = FStar_Syntax_Syntax.iarg t_b in
        let uu____451 =
          let uu____453 =
            let uu____454 = embed_a (fst x) in
            FStar_Syntax_Syntax.as_arg uu____454 in
          let uu____455 =
            let uu____457 =
              let uu____458 = embed_b (snd x) in
              FStar_Syntax_Syntax.as_arg uu____458 in
            [uu____457] in
          uu____453 :: uu____455 in
        uu____450 :: uu____451 in
      uu____447 :: uu____448 in
    FStar_Syntax_Syntax.mk_Tm_app uu____444 uu____446 in
  uu____443 None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____500 = FStar_Syntax_Util.head_and_args pair in
  match uu____500 with
  | (hd1,args) ->
      let uu____528 =
        let uu____536 =
          let uu____537 = FStar_Syntax_Util.un_uinst hd1 in
          uu____537.FStar_Syntax_Syntax.n in
        (uu____536, args) in
      (match uu____528 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____548::uu____549::(a,uu____551)::(b,uu____553)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____595 = unembed_a a in
           let uu____596 = unembed_b b in (uu____595, uu____596)
       | uu____597 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | None  ->
      let uu____635 =
        let uu____636 =
          let uu____637 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____637
            [FStar_Syntax_Syntax.U_zero] in
        let uu____638 =
          let uu____639 = FStar_Syntax_Syntax.iarg typ in [uu____639] in
        FStar_Syntax_Syntax.mk_Tm_app uu____636 uu____638 in
      uu____635 None FStar_Range.dummyRange
  | Some a ->
      let uu____645 =
        let uu____646 =
          let uu____647 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____647
            [FStar_Syntax_Syntax.U_zero] in
        let uu____648 =
          let uu____649 = FStar_Syntax_Syntax.iarg typ in
          let uu____650 =
            let uu____652 =
              let uu____653 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____653 in
            [uu____652] in
          uu____649 :: uu____650 in
        FStar_Syntax_Syntax.mk_Tm_app uu____646 uu____648 in
      uu____645 None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____679 = FStar_Syntax_Util.head_and_args o in
  match uu____679 with
  | (hd1,args) ->
      let uu____706 =
        let uu____714 =
          let uu____715 = FStar_Syntax_Util.un_uinst hd1 in
          uu____715.FStar_Syntax_Syntax.n in
        (uu____714, args) in
      (match uu____706 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____725) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.none_lid ->
           None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____737::(a,uu____739)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.some_lid ->
           let uu____765 = unembed_a a in Some uu____765
       | uu____766 -> failwith "Not an embedded option")
let embed_fvar: FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  -> FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar" None
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____783 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____783 FStar_Dyn.undyn
let embed_const:
  FStar_Reflection_Data.vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
    | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
    | FStar_Reflection_Data.C_Int i ->
        let uu____789 =
          let uu____790 =
            let uu____791 =
              let uu____792 =
                let uu____793 = FStar_Util.string_of_int i in
                FStar_Syntax_Const.exp_int uu____793 in
              FStar_Syntax_Syntax.as_arg uu____792 in
            [uu____791] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____790 in
        uu____789 None FStar_Range.dummyRange
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____803 =
          let uu____804 =
            let uu____805 =
              let uu____806 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____806 in
            [uu____805] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____804 in
        uu____803 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____812 =
          let uu____813 =
            let uu____814 =
              let uu____815 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____815 in
            [uu____814] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____813 in
        uu____812 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____822 =
          let uu____823 =
            let uu____824 =
              let uu____825 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____825 in
            let uu____826 =
              let uu____828 =
                let uu____829 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____829 in
              [uu____828] in
            uu____824 :: uu____826 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____823 in
        uu____822 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____836 =
          let uu____837 =
            let uu____838 =
              let uu____839 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____839 in
            let uu____840 =
              let uu____842 =
                let uu____843 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____843 in
              [uu____842] in
            uu____838 :: uu____840 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____837 in
        uu____836 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____850 =
          let uu____851 =
            let uu____852 =
              let uu____853 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____853 in
            let uu____854 =
              let uu____856 =
                let uu____857 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____857 in
              [uu____856] in
            uu____852 :: uu____854 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____851 in
        uu____850 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____863 =
          let uu____864 =
            let uu____865 =
              let uu____866 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____866 in
            [uu____865] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____864 in
        uu____863 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____873 =
          let uu____874 =
            let uu____875 =
              let uu____876 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____876 in
            let uu____877 =
              let uu____879 =
                let uu____880 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____880 in
              [uu____879] in
            uu____875 :: uu____877 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____874 in
        uu____873 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____886 =
          let uu____887 =
            let uu____888 =
              let uu____889 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____889 in
            [uu____888] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____887 in
        uu____886 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____899 = FStar_Syntax_Util.head_and_args t1 in
    match uu____899 with
    | (hd1,args) ->
        let uu____925 =
          let uu____933 =
            let uu____934 = FStar_Syntax_Util.un_uinst hd1 in
            uu____934.FStar_Syntax_Syntax.n in
          (uu____933, args) in
        (match uu____925 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit_lid
             -> FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_True_lid
             -> FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_False_lid
             -> FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____974)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____992 =
               let uu____993 = FStar_Syntax_Subst.compress i in
               uu____993.FStar_Syntax_Syntax.n in
             (match uu____992 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____997)) ->
                  let uu____1004 = FStar_Util.int_of_string s in
                  FStar_Reflection_Data.C_Int uu____1004
              | uu____1005 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____1006 -> failwith "not an embedded vconst")
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1019 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1019 with
    | (hd1,args) ->
        let uu____1045 =
          let uu____1053 =
            let uu____1054 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1054.FStar_Syntax_Syntax.n in
          (uu____1053, args) in
        (match uu____1045 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1064)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1082 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1082
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1085)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1103 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1103
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1106)::(r,uu____1108)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1134 =
               let uu____1137 = unembed_term l in
               let uu____1138 = unembed_term r in (uu____1137, uu____1138) in
             FStar_Reflection_Data.Tv_App uu____1134
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1141)::(t2,uu____1143)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1169 =
               let uu____1172 = unembed_binder b in
               let uu____1173 = unembed_term t2 in (uu____1172, uu____1173) in
             FStar_Reflection_Data.Tv_Abs uu____1169
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1176)::(t2,uu____1178)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1204 =
               let uu____1207 = unembed_binder b in
               let uu____1208 = unembed_term t2 in (uu____1207, uu____1208) in
             FStar_Reflection_Data.Tv_Arrow uu____1204
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1211)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1232)::(t2,uu____1234)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1260 =
               let uu____1263 = unembed_binder b in
               let uu____1264 = unembed_term t2 in (uu____1263, uu____1264) in
             FStar_Reflection_Data.Tv_Refine uu____1260
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1267)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1285 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1285
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1296 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1316::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1336 = init xs in x :: uu____1336
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1344 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1344
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1351 = FStar_Syntax_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1351
      FStar_Syntax_Syntax.Delta_equational None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (fst b)
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1362 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1362
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1394 = last args in
        (match uu____1394 with
         | (a,uu____1404) ->
             let uu____1409 =
               let uu____1412 =
                 let uu____1415 =
                   let uu____1416 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1416 in
                 uu____1415 None t1.FStar_Syntax_Syntax.pos in
               (uu____1412, a) in
             FStar_Reflection_Data.Tv_App uu____1409)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1429,uu____1430) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1457 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1457 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1473 =
                    let uu____1476 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1476) in
                  FStar_Reflection_Data.Tv_Abs uu____1473))
    | FStar_Syntax_Syntax.Tm_type uu____1479 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1502 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1502 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1518 =
                    let uu____1521 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1521) in
                  FStar_Reflection_Data.Tv_Arrow uu____1518))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1535 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1535 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1552 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
          | FStar_Const.Const_int (s,uu____1560) ->
              let uu____1567 = FStar_Util.int_of_string s in
              FStar_Reflection_Data.C_Int uu____1567
          | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
          | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
          | uu____1568 ->
              let uu____1569 =
                let uu____1570 = FStar_Syntax_Print.const_to_string c in
                FStar_Util.format1 "unknown constant: %s" uu____1570 in
              failwith uu____1569 in
        FStar_Reflection_Data.Tv_Const c1
    | uu____1571 ->
        ((let uu____1573 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1574 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1573 uu____1574);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Syntax_Const.exp_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____1580 = FStar_Util.string_of_int i in
        FStar_Syntax_Const.exp_int uu____1580
    | FStar_Reflection_Data.C_True  -> FStar_Syntax_Const.exp_true_bool
    | FStar_Reflection_Data.C_False  -> FStar_Syntax_Const.exp_false_bool
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1586) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1590 =
          let uu____1596 = FStar_Syntax_Syntax.as_arg r in [uu____1596] in
        FStar_Syntax_Util.mk_app l uu____1590
    | FStar_Reflection_Data.Tv_Abs (b,t) -> FStar_Syntax_Util.abs [b] t None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1601 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1601
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1605),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c -> pack_const c
    | uu____1610 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1620 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1620 with
    | (hd1,args) ->
        let uu____1646 =
          let uu____1654 =
            let uu____1655 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1655.FStar_Syntax_Syntax.n in
          (uu____1654, args) in
        (match uu____1646 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Lt_lid
             -> FStar_Reflection_Data.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Eq_lid
             -> FStar_Reflection_Data.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Gt_lid
             -> FStar_Reflection_Data.Gt
         | uu____1693 -> failwith "not an embedded order")
let order_binder:
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Reflection_Data.order
  =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv (fst x) (fst y) in
      if n1 < (Prims.parse_int "0")
      then FStar_Reflection_Data.Lt
      else
        if n1 = (Prims.parse_int "0")
        then FStar_Reflection_Data.Eq
        else FStar_Reflection_Data.Gt
let is_free:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  -> fun t  -> FStar_Syntax_Util.is_free_in (fst x) t
let embed_norm_step:
  FStar_Reflection_Data.norm_step -> FStar_Syntax_Syntax.term =
  fun n1  ->
    match n1 with
    | FStar_Reflection_Data.Simpl  -> FStar_Reflection_Data.ref_Simpl
    | FStar_Reflection_Data.WHNF  -> FStar_Reflection_Data.ref_WHNF
    | FStar_Reflection_Data.Primops  -> FStar_Reflection_Data.ref_Primops
    | FStar_Reflection_Data.Delta  -> FStar_Reflection_Data.ref_Delta
let unembed_norm_step:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.norm_step =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1729 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1729 with
    | (hd1,args) ->
        let uu____1755 =
          let uu____1763 =
            let uu____1764 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1764.FStar_Syntax_Syntax.n in
          (uu____1763, args) in
        (match uu____1755 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Simpl_lid
             -> FStar_Reflection_Data.Simpl
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_WHNF_lid
             -> FStar_Reflection_Data.WHNF
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Primops_lid
             -> FStar_Reflection_Data.Primops
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Delta_lid
             -> FStar_Reflection_Data.Delta
         | uu____1812 -> failwith "not an embedded norm_step")