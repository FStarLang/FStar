open Prims
let protect_embedded_term:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____9 =
        let uu____10 =
          let uu____11 = FStar_Syntax_Syntax.iarg t in
          let uu____12 =
            let uu____14 = FStar_Syntax_Syntax.as_arg x in [uu____14] in
          uu____11 :: uu____12 in
        FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Const.fstar_refl_embed
          uu____10 in
      uu____9 None x.FStar_Syntax_Syntax.pos
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____22 = FStar_Syntax_Util.head_and_args t in
    match uu____22 with
    | (head1,args) ->
        let uu____48 =
          let uu____56 =
            let uu____57 = FStar_Syntax_Util.un_uinst head1 in
            uu____57.FStar_Syntax_Syntax.n in
          (uu____56, args) in
        (match uu____48 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____66::(x,uu____68)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Syntax_Const.fstar_refl_embed_lid
             -> x
         | uu____94 ->
             let uu____102 =
               let uu____103 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term (2): %s"
                 uu____103 in
             failwith uu____102)
let type_of_embedded: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ =
  fun t  ->
    let uu____107 = FStar_Syntax_Util.head_and_args t in
    match uu____107 with
    | (head1,args) ->
        let uu____133 =
          let uu____141 =
            let uu____142 = FStar_Syntax_Util.un_uinst head1 in
            uu____142.FStar_Syntax_Syntax.n in
          (uu____141, args) in
        (match uu____133 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t1,uu____152)::uu____153::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Syntax_Const.fstar_refl_embed_lid
             -> t1
         | uu____179 ->
             let uu____187 =
               let uu____188 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term (1): %s"
                 uu____188 in
             failwith uu____187)
let embed_unit: Prims.unit -> FStar_Syntax_Syntax.term =
  fun u  -> FStar_Syntax_Const.exp_unit
let unembed_unit: FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____194  -> ()
let embed_bool: Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Const.exp_true_bool
    else FStar_Syntax_Const.exp_false_bool
let unembed_bool: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____202 =
      let uu____203 = FStar_Syntax_Subst.compress t in
      uu____203.FStar_Syntax_Syntax.n in
    match uu____202 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____207 -> failwith "Not an embedded bool"
let embed_string:
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s in
    (FStar_Syntax_Syntax.mk
       (FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (bytes, FStar_Range.dummyRange)))) None
      FStar_Range.dummyRange
let unembed_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____227)) -> FStar_Util.string_of_unicode bytes
    | uu____230 ->
        let uu____231 =
          let uu____232 =
            let uu____233 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____233 ")" in
          Prims.strcat "Not an embedded string (" uu____232 in
        failwith uu____231
let lid_Mktuple2: FStar_Ident.lident =
  FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2")
    FStar_Range.dummyRange
let lid_tuple2: FStar_Ident.lident =
  FStar_Syntax_Util.mk_tuple_lid (Prims.parse_int "2") FStar_Range.dummyRange
let embed_binder:
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    let uu____237 = FStar_Syntax_Syntax.bv_to_name (Prims.fst b) in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_binder uu____237
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Syntax_Syntax.mk_binder bv
    | uu____244 -> failwith "Not an embedded binder"
let rec embed_list embed_a typ l =
  match l with
  | [] ->
      let uu____269 =
        let uu____270 =
          let uu____271 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____271
            [FStar_Syntax_Syntax.U_zero] in
        let uu____272 =
          let uu____273 = FStar_Syntax_Syntax.iarg typ in [uu____273] in
        FStar_Syntax_Syntax.mk_Tm_app uu____270 uu____272 in
      uu____269 None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____281 =
        let uu____282 =
          let uu____283 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____283
            [FStar_Syntax_Syntax.U_zero] in
        let uu____284 =
          let uu____285 = FStar_Syntax_Syntax.iarg typ in
          let uu____286 =
            let uu____288 =
              let uu____289 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____289 in
            let uu____290 =
              let uu____292 =
                let uu____293 = embed_list embed_a typ tl1 in
                FStar_Syntax_Syntax.as_arg uu____293 in
              [uu____292] in
            uu____288 :: uu____290 in
          uu____285 :: uu____286 in
        FStar_Syntax_Syntax.mk_Tm_app uu____282 uu____284 in
      uu____281 None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____317 = FStar_Syntax_Util.head_and_args l1 in
  match uu____317 with
  | (hd1,args) ->
      let uu____344 =
        let uu____352 =
          let uu____353 = FStar_Syntax_Util.un_uinst hd1 in
          uu____353.FStar_Syntax_Syntax.n in
        (uu____352, args) in
      (match uu____344 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____363) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____377)::(tl1,uu____379)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
           let uu____413 = unembed_a hd2 in
           let uu____414 = unembed_list unembed_a tl1 in uu____413 ::
             uu____414
       | uu____416 ->
           let uu____424 =
             let uu____425 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____425 in
           failwith uu____424)
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
  let uu____485 =
    let uu____486 =
      let uu____487 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____487
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____488 =
      let uu____489 = FStar_Syntax_Syntax.iarg t_a in
      let uu____490 =
        let uu____492 = FStar_Syntax_Syntax.iarg t_b in
        let uu____493 =
          let uu____495 =
            let uu____496 = embed_a (Prims.fst x) in
            FStar_Syntax_Syntax.as_arg uu____496 in
          let uu____497 =
            let uu____499 =
              let uu____500 = embed_b (Prims.snd x) in
              FStar_Syntax_Syntax.as_arg uu____500 in
            [uu____499] in
          uu____495 :: uu____497 in
        uu____492 :: uu____493 in
      uu____489 :: uu____490 in
    FStar_Syntax_Syntax.mk_Tm_app uu____486 uu____488 in
  uu____485 None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____537 = FStar_Syntax_Util.head_and_args pair in
  match uu____537 with
  | (hd1,args) ->
      let uu____565 =
        let uu____573 =
          let uu____574 = FStar_Syntax_Util.un_uinst hd1 in
          uu____574.FStar_Syntax_Syntax.n in
        (uu____573, args) in
      (match uu____565 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____585::uu____586::(a,uu____588)::(b,uu____590)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____632 = unembed_a a in
           let uu____633 = unembed_b b in (uu____632, uu____633)
       | uu____634 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | None  ->
      let uu____668 =
        let uu____669 =
          let uu____670 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____670
            [FStar_Syntax_Syntax.U_zero] in
        let uu____671 =
          let uu____672 = FStar_Syntax_Syntax.iarg typ in [uu____672] in
        FStar_Syntax_Syntax.mk_Tm_app uu____669 uu____671 in
      uu____668 None FStar_Range.dummyRange
  | Some a ->
      let uu____678 =
        let uu____679 =
          let uu____680 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____680
            [FStar_Syntax_Syntax.U_zero] in
        let uu____681 =
          let uu____682 = FStar_Syntax_Syntax.iarg typ in
          let uu____683 =
            let uu____685 =
              let uu____686 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____686 in
            [uu____685] in
          uu____682 :: uu____683 in
        FStar_Syntax_Syntax.mk_Tm_app uu____679 uu____681 in
      uu____678 None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____709 = FStar_Syntax_Util.head_and_args o in
  match uu____709 with
  | (hd1,args) ->
      let uu____736 =
        let uu____744 =
          let uu____745 = FStar_Syntax_Util.un_uinst hd1 in
          uu____745.FStar_Syntax_Syntax.n in
        (uu____744, args) in
      (match uu____736 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____755) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.none_lid ->
           None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____767::(a,uu____769)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.some_lid ->
           let uu____795 = unembed_a a in Some uu____795
       | uu____796 -> failwith "Not an embedded option")
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____808 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_fvar uu____808
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____815 -> failwith "Not an embedded fv"
let embed_const:
  FStar_Reflection_Data.vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_Int s ->
        let uu____820 =
          let uu____821 =
            let uu____822 =
              let uu____823 = FStar_Syntax_Const.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____823 in
            [uu____822] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____821 in
        uu____820 None FStar_Range.dummyRange
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____832 =
          let uu____833 =
            let uu____834 =
              let uu____835 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____835 in
            [uu____834] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____833 in
        uu____832 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____841 =
          let uu____842 =
            let uu____843 =
              let uu____844 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____844 in
            [uu____843] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____842 in
        uu____841 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____851 =
          let uu____852 =
            let uu____853 =
              let uu____854 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____854 in
            let uu____855 =
              let uu____857 =
                let uu____858 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____858 in
              [uu____857] in
            uu____853 :: uu____855 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____852 in
        uu____851 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____865 =
          let uu____866 =
            let uu____867 =
              let uu____868 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____868 in
            let uu____869 =
              let uu____871 =
                let uu____872 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____872 in
              [uu____871] in
            uu____867 :: uu____869 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____866 in
        uu____865 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____879 =
          let uu____880 =
            let uu____881 =
              let uu____882 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____882 in
            let uu____883 =
              let uu____885 =
                let uu____886 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____886 in
              [uu____885] in
            uu____881 :: uu____883 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____880 in
        uu____879 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____892 =
          let uu____893 =
            let uu____894 =
              let uu____895 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____895 in
            [uu____894] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____893 in
        uu____892 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____902 =
          let uu____903 =
            let uu____904 =
              let uu____905 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____905 in
            let uu____906 =
              let uu____908 =
                let uu____909 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____909 in
              [uu____908] in
            uu____904 :: uu____906 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____903 in
        uu____902 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____915 =
          let uu____916 =
            let uu____917 =
              let uu____918 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____918 in
            [uu____917] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____916 in
        uu____915 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____927 = FStar_Syntax_Util.head_and_args t1 in
    match uu____927 with
    | (hd1,args) ->
        let uu____953 =
          let uu____961 =
            let uu____962 = FStar_Syntax_Util.un_uinst hd1 in
            uu____962.FStar_Syntax_Syntax.n in
          (uu____961, args) in
        (match uu____953 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit_lid
             -> FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____982)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____1000 =
               let uu____1001 = FStar_Syntax_Subst.compress i in
               uu____1001.FStar_Syntax_Syntax.n in
             (match uu____1000 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____1005)) -> FStar_Reflection_Data.C_Int s
              | uu____1012 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____1013 -> failwith "not an embedded vconst")
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1025 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1025 with
    | (hd1,args) ->
        let uu____1051 =
          let uu____1059 =
            let uu____1060 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1060.FStar_Syntax_Syntax.n in
          (uu____1059, args) in
        (match uu____1051 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1070)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1088 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1088
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1091)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1109 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1109
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1112)::(r,uu____1114)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1140 =
               let uu____1143 = unembed_term l in
               let uu____1144 = unembed_term r in (uu____1143, uu____1144) in
             FStar_Reflection_Data.Tv_App uu____1140
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1147)::(t2,uu____1149)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1175 =
               let uu____1178 = unembed_binder b in
               let uu____1179 = unembed_term t2 in (uu____1178, uu____1179) in
             FStar_Reflection_Data.Tv_Abs uu____1175
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1182)::(t2,uu____1184)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1210 =
               let uu____1213 = unembed_binder b in
               let uu____1214 = unembed_term t2 in (uu____1213, uu____1214) in
             FStar_Reflection_Data.Tv_Arrow uu____1210
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1217)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1238)::(t2,uu____1240)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1266 =
               let uu____1269 = unembed_binder b in
               let uu____1270 = unembed_term t2 in (uu____1269, uu____1270) in
             FStar_Reflection_Data.Tv_Refine uu____1266
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1273)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1291 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1291
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1302 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1320::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1338 = init xs in x :: uu____1338
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1345 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1345
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1351 = FStar_Syntax_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1351
      FStar_Syntax_Syntax.Delta_equational None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (Prims.fst b)
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1360 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1360
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1392 = last args in
        (match uu____1392 with
         | (a,uu____1402) ->
             let uu____1407 =
               let uu____1410 =
                 let uu____1413 =
                   let uu____1414 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1414 in
                 uu____1413 None t1.FStar_Syntax_Syntax.pos in
               (uu____1410, a) in
             FStar_Reflection_Data.Tv_App uu____1407)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1427,uu____1428) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1475 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1475 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1491 =
                    let uu____1494 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1494) in
                  FStar_Reflection_Data.Tv_Abs uu____1491))
    | FStar_Syntax_Syntax.Tm_type uu____1497 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1520 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1520 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1536 =
                    let uu____1539 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1539) in
                  FStar_Reflection_Data.Tv_Arrow uu____1536))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1553 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1553 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1570 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
          | FStar_Const.Const_int (s,uu____1578) ->
              FStar_Reflection_Data.C_Int s
          | uu____1585 ->
              let uu____1586 =
                let uu____1587 = FStar_Syntax_Print.const_to_string c in
                FStar_Util.format1 "unknown constant: %s" uu____1587 in
              failwith uu____1586 in
        FStar_Reflection_Data.Tv_Const c1
    | uu____1588 ->
        ((let uu____1590 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1591 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1590 uu____1591);
         FStar_Reflection_Data.Tv_Unknown)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1596) ->
        FStar_Syntax_Syntax.bv_to_tm bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1600 =
          let uu____1606 = FStar_Syntax_Syntax.as_arg r in [uu____1606] in
        FStar_Syntax_Util.mk_app l uu____1600
    | FStar_Reflection_Data.Tv_Abs (b,t) -> FStar_Syntax_Util.abs [b] t None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1616 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1616
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1620),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Unit ) ->
        FStar_Syntax_Const.exp_unit
    | FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int s) ->
        FStar_Syntax_Const.exp_int s
    | uu____1625 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1633 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1633 with
    | (hd1,args) ->
        let uu____1659 =
          let uu____1667 =
            let uu____1668 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1668.FStar_Syntax_Syntax.n in
          (uu____1667, args) in
        (match uu____1659 with
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
         | uu____1706 -> failwith "not an embedded order")
let order_binder:
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Reflection_Data.order
  =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv (Prims.fst x) (Prims.fst y) in
      if n1 < (Prims.parse_int "0")
      then FStar_Reflection_Data.Lt
      else
        if n1 = (Prims.parse_int "0")
        then FStar_Reflection_Data.Eq
        else FStar_Reflection_Data.Gt
let is_free:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    fun t  ->
      let uu____1729 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem (Prims.fst x) uu____1729