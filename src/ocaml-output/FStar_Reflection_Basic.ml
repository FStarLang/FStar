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
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____103 in
             failwith uu____102)
let embed_unit: Prims.unit -> FStar_Syntax_Syntax.term =
  fun u  -> FStar_Syntax_Const.exp_unit
let unembed_unit: FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____109  -> ()
let embed_bool: Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Const.exp_true_bool
    else FStar_Syntax_Const.exp_false_bool
let unembed_bool: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____117 =
      let uu____118 = FStar_Syntax_Subst.compress t in
      uu____118.FStar_Syntax_Syntax.n in
    match uu____117 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____122 -> failwith "Not an embedded bool"
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
        (bytes,uu____138)) -> FStar_Util.string_of_unicode bytes
    | uu____141 ->
        let uu____142 =
          let uu____143 =
            let uu____144 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____144 ")" in
          Prims.strcat "Not an embedded string (" uu____143 in
        failwith uu____142
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
    let uu____148 = FStar_Syntax_Syntax.bv_to_name (fst b) in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_binder uu____148
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Syntax_Syntax.mk_binder bv
    | uu____155 -> failwith "Not an embedded binder"
let rec embed_list embed_a typ l =
  match l with
  | [] ->
      let uu____180 =
        let uu____181 =
          let uu____182 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____182
            [FStar_Syntax_Syntax.U_zero] in
        let uu____183 =
          let uu____184 = FStar_Syntax_Syntax.iarg typ in [uu____184] in
        FStar_Syntax_Syntax.mk_Tm_app uu____181 uu____183 in
      uu____180 None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____192 =
        let uu____193 =
          let uu____194 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____194
            [FStar_Syntax_Syntax.U_zero] in
        let uu____195 =
          let uu____196 = FStar_Syntax_Syntax.iarg typ in
          let uu____197 =
            let uu____199 =
              let uu____200 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____200 in
            let uu____201 =
              let uu____203 =
                let uu____204 = embed_list embed_a typ tl1 in
                FStar_Syntax_Syntax.as_arg uu____204 in
              [uu____203] in
            uu____199 :: uu____201 in
          uu____196 :: uu____197 in
        FStar_Syntax_Syntax.mk_Tm_app uu____193 uu____195 in
      uu____192 None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____228 = FStar_Syntax_Util.head_and_args l1 in
  match uu____228 with
  | (hd1,args) ->
      let uu____255 =
        let uu____263 =
          let uu____264 = FStar_Syntax_Util.un_uinst hd1 in
          uu____264.FStar_Syntax_Syntax.n in
        (uu____263, args) in
      (match uu____255 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____274) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____288)::(tl1,uu____290)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
           let uu____324 = unembed_a hd2 in
           let uu____325 = unembed_list unembed_a tl1 in uu____324 ::
             uu____325
       | uu____327 ->
           let uu____335 =
             let uu____336 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____336 in
           failwith uu____335)
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
  let uu____396 =
    let uu____397 =
      let uu____398 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____398
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____399 =
      let uu____400 = FStar_Syntax_Syntax.iarg t_a in
      let uu____401 =
        let uu____403 = FStar_Syntax_Syntax.iarg t_b in
        let uu____404 =
          let uu____406 =
            let uu____407 = embed_a (fst x) in
            FStar_Syntax_Syntax.as_arg uu____407 in
          let uu____408 =
            let uu____410 =
              let uu____411 = embed_b (snd x) in
              FStar_Syntax_Syntax.as_arg uu____411 in
            [uu____410] in
          uu____406 :: uu____408 in
        uu____403 :: uu____404 in
      uu____400 :: uu____401 in
    FStar_Syntax_Syntax.mk_Tm_app uu____397 uu____399 in
  uu____396 None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____448 = FStar_Syntax_Util.head_and_args pair in
  match uu____448 with
  | (hd1,args) ->
      let uu____476 =
        let uu____484 =
          let uu____485 = FStar_Syntax_Util.un_uinst hd1 in
          uu____485.FStar_Syntax_Syntax.n in
        (uu____484, args) in
      (match uu____476 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____496::uu____497::(a,uu____499)::(b,uu____501)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____543 = unembed_a a in
           let uu____544 = unembed_b b in (uu____543, uu____544)
       | uu____545 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | None  ->
      let uu____579 =
        let uu____580 =
          let uu____581 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____581
            [FStar_Syntax_Syntax.U_zero] in
        let uu____582 =
          let uu____583 = FStar_Syntax_Syntax.iarg typ in [uu____583] in
        FStar_Syntax_Syntax.mk_Tm_app uu____580 uu____582 in
      uu____579 None FStar_Range.dummyRange
  | Some a ->
      let uu____589 =
        let uu____590 =
          let uu____591 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____591
            [FStar_Syntax_Syntax.U_zero] in
        let uu____592 =
          let uu____593 = FStar_Syntax_Syntax.iarg typ in
          let uu____594 =
            let uu____596 =
              let uu____597 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____597 in
            [uu____596] in
          uu____593 :: uu____594 in
        FStar_Syntax_Syntax.mk_Tm_app uu____590 uu____592 in
      uu____589 None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____620 = FStar_Syntax_Util.head_and_args o in
  match uu____620 with
  | (hd1,args) ->
      let uu____647 =
        let uu____655 =
          let uu____656 = FStar_Syntax_Util.un_uinst hd1 in
          uu____656.FStar_Syntax_Syntax.n in
        (uu____655, args) in
      (match uu____647 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____666) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.none_lid ->
           None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____678::(a,uu____680)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.some_lid ->
           let uu____706 = unembed_a a in Some uu____706
       | uu____707 -> failwith "Not an embedded option")
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____719 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_fvar uu____719
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____726 -> failwith "Not an embedded fv"
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
    | FStar_Reflection_Data.C_Int s ->
        let uu____731 =
          let uu____732 =
            let uu____733 =
              let uu____734 = FStar_Syntax_Const.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____734 in
            [uu____733] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____732 in
        uu____731 None FStar_Range.dummyRange
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____743 =
          let uu____744 =
            let uu____745 =
              let uu____746 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____746 in
            [uu____745] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____744 in
        uu____743 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____752 =
          let uu____753 =
            let uu____754 =
              let uu____755 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____755 in
            [uu____754] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____753 in
        uu____752 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____762 =
          let uu____763 =
            let uu____764 =
              let uu____765 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____765 in
            let uu____766 =
              let uu____768 =
                let uu____769 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____769 in
              [uu____768] in
            uu____764 :: uu____766 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____763 in
        uu____762 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____776 =
          let uu____777 =
            let uu____778 =
              let uu____779 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____779 in
            let uu____780 =
              let uu____782 =
                let uu____783 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____783 in
              [uu____782] in
            uu____778 :: uu____780 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____777 in
        uu____776 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____790 =
          let uu____791 =
            let uu____792 =
              let uu____793 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____793 in
            let uu____794 =
              let uu____796 =
                let uu____797 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____797 in
              [uu____796] in
            uu____792 :: uu____794 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____791 in
        uu____790 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____803 =
          let uu____804 =
            let uu____805 =
              let uu____806 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____806 in
            [uu____805] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____804 in
        uu____803 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____813 =
          let uu____814 =
            let uu____815 =
              let uu____816 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____816 in
            let uu____817 =
              let uu____819 =
                let uu____820 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____820 in
              [uu____819] in
            uu____815 :: uu____817 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____814 in
        uu____813 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____826 =
          let uu____827 =
            let uu____828 =
              let uu____829 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____829 in
            [uu____828] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____827 in
        uu____826 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____838 = FStar_Syntax_Util.head_and_args t1 in
    match uu____838 with
    | (hd1,args) ->
        let uu____864 =
          let uu____872 =
            let uu____873 = FStar_Syntax_Util.un_uinst hd1 in
            uu____873.FStar_Syntax_Syntax.n in
          (uu____872, args) in
        (match uu____864 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____913)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____931 =
               let uu____932 = FStar_Syntax_Subst.compress i in
               uu____932.FStar_Syntax_Syntax.n in
             (match uu____931 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____936)) -> FStar_Reflection_Data.C_Int s
              | uu____943 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____944 -> failwith "not an embedded vconst")
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____956 = FStar_Syntax_Util.head_and_args t1 in
    match uu____956 with
    | (hd1,args) ->
        let uu____982 =
          let uu____990 =
            let uu____991 = FStar_Syntax_Util.un_uinst hd1 in
            uu____991.FStar_Syntax_Syntax.n in
          (uu____990, args) in
        (match uu____982 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1001)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1019 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1019
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1022)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1040 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1040
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1043)::(r,uu____1045)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1071 =
               let uu____1074 = unembed_term l in
               let uu____1075 = unembed_term r in (uu____1074, uu____1075) in
             FStar_Reflection_Data.Tv_App uu____1071
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1078)::(t2,uu____1080)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1106 =
               let uu____1109 = unembed_binder b in
               let uu____1110 = unembed_term t2 in (uu____1109, uu____1110) in
             FStar_Reflection_Data.Tv_Abs uu____1106
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1113)::(t2,uu____1115)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1141 =
               let uu____1144 = unembed_binder b in
               let uu____1145 = unembed_term t2 in (uu____1144, uu____1145) in
             FStar_Reflection_Data.Tv_Arrow uu____1141
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1148)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1169)::(t2,uu____1171)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1197 =
               let uu____1200 = unembed_binder b in
               let uu____1201 = unembed_term t2 in (uu____1200, uu____1201) in
             FStar_Reflection_Data.Tv_Refine uu____1197
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1204)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1222 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1222
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1233 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1251::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1269 = init xs in x :: uu____1269
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1276 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1276
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1282 = FStar_Syntax_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1282
      FStar_Syntax_Syntax.Delta_equational None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (fst b)
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1291 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1291
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1323 = last args in
        (match uu____1323 with
         | (a,uu____1333) ->
             let uu____1338 =
               let uu____1341 =
                 let uu____1344 =
                   let uu____1345 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1345 in
                 uu____1344 None t1.FStar_Syntax_Syntax.pos in
               (uu____1341, a) in
             FStar_Reflection_Data.Tv_App uu____1338)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1358,uu____1359) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1406 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1406 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1422 =
                    let uu____1425 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1425) in
                  FStar_Reflection_Data.Tv_Abs uu____1422))
    | FStar_Syntax_Syntax.Tm_type uu____1428 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1451 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1451 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1467 =
                    let uu____1470 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1470) in
                  FStar_Reflection_Data.Tv_Arrow uu____1467))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1484 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1484 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1501 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
          | FStar_Const.Const_int (s,uu____1509) ->
              FStar_Reflection_Data.C_Int s
          | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
          | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
          | uu____1516 ->
              let uu____1517 =
                let uu____1518 = FStar_Syntax_Print.const_to_string c in
                FStar_Util.format1 "unknown constant: %s" uu____1518 in
              failwith uu____1517 in
        FStar_Reflection_Data.Tv_Const c1
    | uu____1519 ->
        ((let uu____1521 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1522 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1521 uu____1522);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Syntax_Const.exp_unit
    | FStar_Reflection_Data.C_Int s -> FStar_Syntax_Const.exp_int s
    | FStar_Reflection_Data.C_True  -> FStar_Syntax_Const.exp_true_bool
    | FStar_Reflection_Data.C_False  -> FStar_Syntax_Const.exp_false_bool
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1531) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1535 =
          let uu____1541 = FStar_Syntax_Syntax.as_arg r in [uu____1541] in
        FStar_Syntax_Util.mk_app l uu____1535
    | FStar_Reflection_Data.Tv_Abs (b,t) -> FStar_Syntax_Util.abs [b] t None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1551 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1551
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1555),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c -> pack_const c
    | uu____1560 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1568 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1568 with
    | (hd1,args) ->
        let uu____1594 =
          let uu____1602 =
            let uu____1603 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1603.FStar_Syntax_Syntax.n in
          (uu____1602, args) in
        (match uu____1594 with
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
         | uu____1641 -> failwith "not an embedded order")
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
    let uu____1671 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1671 with
    | (hd1,args) ->
        let uu____1697 =
          let uu____1705 =
            let uu____1706 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1706.FStar_Syntax_Syntax.n in
          (uu____1705, args) in
        (match uu____1697 with
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
         | uu____1754 -> failwith "not an embedded norm_step")