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
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (bytes, FStar_Range.dummyRange))) None
      FStar_Range.dummyRange
let unembed_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____223)) -> FStar_Util.string_of_unicode bytes
    | uu____226 ->
        let uu____227 =
          let uu____228 =
            let uu____229 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____229 ")" in
          Prims.strcat "Not an embedded string (" uu____228 in
        failwith uu____227
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
    let uu____233 = FStar_Syntax_Syntax.bv_to_name (fst b) in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_binder uu____233
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Syntax_Syntax.mk_binder bv
    | uu____240 -> failwith "Not an embedded binder"
let rec embed_list embed_a typ l =
  match l with
  | [] ->
      let uu____265 =
        let uu____266 =
          let uu____267 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____267
            [FStar_Syntax_Syntax.U_zero] in
        let uu____268 =
          let uu____269 = FStar_Syntax_Syntax.iarg typ in [uu____269] in
        FStar_Syntax_Syntax.mk_Tm_app uu____266 uu____268 in
      uu____265 None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____277 =
        let uu____278 =
          let uu____279 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____279
            [FStar_Syntax_Syntax.U_zero] in
        let uu____280 =
          let uu____281 = FStar_Syntax_Syntax.iarg typ in
          let uu____282 =
            let uu____284 =
              let uu____285 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____285 in
            let uu____286 =
              let uu____288 =
                let uu____289 = embed_list embed_a typ tl1 in
                FStar_Syntax_Syntax.as_arg uu____289 in
              [uu____288] in
            uu____284 :: uu____286 in
          uu____281 :: uu____282 in
        FStar_Syntax_Syntax.mk_Tm_app uu____278 uu____280 in
      uu____277 None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____313 = FStar_Syntax_Util.head_and_args l1 in
  match uu____313 with
  | (hd1,args) ->
      let uu____340 =
        let uu____348 =
          let uu____349 = FStar_Syntax_Util.un_uinst hd1 in
          uu____349.FStar_Syntax_Syntax.n in
        (uu____348, args) in
      (match uu____340 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____359) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____373)::(tl1,uu____375)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
           let uu____409 = unembed_a hd2 in
           let uu____410 = unembed_list unembed_a tl1 in uu____409 ::
             uu____410
       | uu____412 ->
           let uu____420 =
             let uu____421 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____421 in
           failwith uu____420)
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
  let uu____481 =
    let uu____482 =
      let uu____483 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____483
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____484 =
      let uu____485 = FStar_Syntax_Syntax.iarg t_a in
      let uu____486 =
        let uu____488 = FStar_Syntax_Syntax.iarg t_b in
        let uu____489 =
          let uu____491 =
            let uu____492 = embed_a (fst x) in
            FStar_Syntax_Syntax.as_arg uu____492 in
          let uu____493 =
            let uu____495 =
              let uu____496 = embed_b (snd x) in
              FStar_Syntax_Syntax.as_arg uu____496 in
            [uu____495] in
          uu____491 :: uu____493 in
        uu____488 :: uu____489 in
      uu____485 :: uu____486 in
    FStar_Syntax_Syntax.mk_Tm_app uu____482 uu____484 in
  uu____481 None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____533 = FStar_Syntax_Util.head_and_args pair in
  match uu____533 with
  | (hd1,args) ->
      let uu____561 =
        let uu____569 =
          let uu____570 = FStar_Syntax_Util.un_uinst hd1 in
          uu____570.FStar_Syntax_Syntax.n in
        (uu____569, args) in
      (match uu____561 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____581::uu____582::(a,uu____584)::(b,uu____586)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____628 = unembed_a a in
           let uu____629 = unembed_b b in (uu____628, uu____629)
       | uu____630 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | None  ->
      let uu____664 =
        let uu____665 =
          let uu____666 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____666
            [FStar_Syntax_Syntax.U_zero] in
        let uu____667 =
          let uu____668 = FStar_Syntax_Syntax.iarg typ in [uu____668] in
        FStar_Syntax_Syntax.mk_Tm_app uu____665 uu____667 in
      uu____664 None FStar_Range.dummyRange
  | Some a ->
      let uu____674 =
        let uu____675 =
          let uu____676 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____676
            [FStar_Syntax_Syntax.U_zero] in
        let uu____677 =
          let uu____678 = FStar_Syntax_Syntax.iarg typ in
          let uu____679 =
            let uu____681 =
              let uu____682 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____682 in
            [uu____681] in
          uu____678 :: uu____679 in
        FStar_Syntax_Syntax.mk_Tm_app uu____675 uu____677 in
      uu____674 None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____705 = FStar_Syntax_Util.head_and_args o in
  match uu____705 with
  | (hd1,args) ->
      let uu____732 =
        let uu____740 =
          let uu____741 = FStar_Syntax_Util.un_uinst hd1 in
          uu____741.FStar_Syntax_Syntax.n in
        (uu____740, args) in
      (match uu____732 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____751) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.none_lid ->
           None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____763::(a,uu____765)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.some_lid ->
           let uu____791 = unembed_a a in Some uu____791
       | uu____792 -> failwith "Not an embedded option")
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____804 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_fvar uu____804
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____811 -> failwith "Not an embedded fv"
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
        let uu____816 =
          let uu____817 =
            let uu____818 =
              let uu____819 = FStar_Syntax_Const.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____819 in
            [uu____818] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____817 in
        uu____816 None FStar_Range.dummyRange
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____828 =
          let uu____829 =
            let uu____830 =
              let uu____831 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____831 in
            [uu____830] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____829 in
        uu____828 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____837 =
          let uu____838 =
            let uu____839 =
              let uu____840 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____840 in
            [uu____839] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____838 in
        uu____837 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____847 =
          let uu____848 =
            let uu____849 =
              let uu____850 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____850 in
            let uu____851 =
              let uu____853 =
                let uu____854 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____854 in
              [uu____853] in
            uu____849 :: uu____851 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____848 in
        uu____847 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____861 =
          let uu____862 =
            let uu____863 =
              let uu____864 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____864 in
            let uu____865 =
              let uu____867 =
                let uu____868 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____868 in
              [uu____867] in
            uu____863 :: uu____865 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____862 in
        uu____861 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____875 =
          let uu____876 =
            let uu____877 =
              let uu____878 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____878 in
            let uu____879 =
              let uu____881 =
                let uu____882 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____882 in
              [uu____881] in
            uu____877 :: uu____879 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____876 in
        uu____875 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____888 =
          let uu____889 =
            let uu____890 =
              let uu____891 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____891 in
            [uu____890] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____889 in
        uu____888 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____898 =
          let uu____899 =
            let uu____900 =
              let uu____901 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____901 in
            let uu____902 =
              let uu____904 =
                let uu____905 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____905 in
              [uu____904] in
            uu____900 :: uu____902 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____899 in
        uu____898 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____911 =
          let uu____912 =
            let uu____913 =
              let uu____914 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____914 in
            [uu____913] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____912 in
        uu____911 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____923 = FStar_Syntax_Util.head_and_args t1 in
    match uu____923 with
    | (hd1,args) ->
        let uu____949 =
          let uu____957 =
            let uu____958 = FStar_Syntax_Util.un_uinst hd1 in
            uu____958.FStar_Syntax_Syntax.n in
          (uu____957, args) in
        (match uu____949 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____998)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____1016 =
               let uu____1017 = FStar_Syntax_Subst.compress i in
               uu____1017.FStar_Syntax_Syntax.n in
             (match uu____1016 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____1021)) -> FStar_Reflection_Data.C_Int s
              | uu____1028 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____1029 -> failwith "not an embedded vconst")
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1041 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1041 with
    | (hd1,args) ->
        let uu____1067 =
          let uu____1075 =
            let uu____1076 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1076.FStar_Syntax_Syntax.n in
          (uu____1075, args) in
        (match uu____1067 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1086)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1104 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1104
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1107)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1125 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1125
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1128)::(r,uu____1130)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1156 =
               let uu____1159 = unembed_term l in
               let uu____1160 = unembed_term r in (uu____1159, uu____1160) in
             FStar_Reflection_Data.Tv_App uu____1156
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1163)::(t2,uu____1165)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1191 =
               let uu____1194 = unembed_binder b in
               let uu____1195 = unembed_term t2 in (uu____1194, uu____1195) in
             FStar_Reflection_Data.Tv_Abs uu____1191
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1198)::(t2,uu____1200)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1226 =
               let uu____1229 = unembed_binder b in
               let uu____1230 = unembed_term t2 in (uu____1229, uu____1230) in
             FStar_Reflection_Data.Tv_Arrow uu____1226
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1233)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1254)::(t2,uu____1256)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1282 =
               let uu____1285 = unembed_binder b in
               let uu____1286 = unembed_term t2 in (uu____1285, uu____1286) in
             FStar_Reflection_Data.Tv_Refine uu____1282
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1289)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1307 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1307
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1318 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1336::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1354 = init xs in x :: uu____1354
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1361 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1361
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1367 = FStar_Syntax_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1367
      FStar_Syntax_Syntax.Delta_equational None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (fst b)
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1376 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1376
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1408 = last args in
        (match uu____1408 with
         | (a,uu____1418) ->
             let uu____1423 =
               let uu____1426 =
                 let uu____1429 =
                   let uu____1430 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1430 in
                 uu____1429 None t1.FStar_Syntax_Syntax.pos in
               (uu____1426, a) in
             FStar_Reflection_Data.Tv_App uu____1423)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1443,uu____1444) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1491 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1491 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1507 =
                    let uu____1510 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1510) in
                  FStar_Reflection_Data.Tv_Abs uu____1507))
    | FStar_Syntax_Syntax.Tm_type uu____1513 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1536 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1536 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1552 =
                    let uu____1555 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1555) in
                  FStar_Reflection_Data.Tv_Arrow uu____1552))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1569 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1569 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1586 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
          | FStar_Const.Const_int (s,uu____1594) ->
              FStar_Reflection_Data.C_Int s
          | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
          | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
          | uu____1601 ->
              let uu____1602 =
                let uu____1603 = FStar_Syntax_Print.const_to_string c in
                FStar_Util.format1 "unknown constant: %s" uu____1603 in
              failwith uu____1602 in
        FStar_Reflection_Data.Tv_Const c1
    | uu____1604 ->
        ((let uu____1606 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1607 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1606 uu____1607);
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
    | FStar_Reflection_Data.Tv_Var (bv,uu____1616) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1620 =
          let uu____1626 = FStar_Syntax_Syntax.as_arg r in [uu____1626] in
        FStar_Syntax_Util.mk_app l uu____1620
    | FStar_Reflection_Data.Tv_Abs (b,t) -> FStar_Syntax_Util.abs [b] t None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1636 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1636
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1640),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c -> pack_const c
    | uu____1645 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1653 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1653 with
    | (hd1,args) ->
        let uu____1679 =
          let uu____1687 =
            let uu____1688 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1688.FStar_Syntax_Syntax.n in
          (uu____1687, args) in
        (match uu____1679 with
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
         | uu____1726 -> failwith "not an embedded order")
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
  fun x  ->
    fun t  ->
      let uu____1749 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem (fst x) uu____1749
let embed_norm_step:
  FStar_Reflection_Data.norm_step -> FStar_Syntax_Syntax.term =
  fun n1  ->
    match n1 with
    | FStar_Reflection_Data.Simpl  -> FStar_Reflection_Data.ref_Simpl
    | FStar_Reflection_Data.WHNF  -> FStar_Reflection_Data.ref_WHNF
    | FStar_Reflection_Data.Primops  -> FStar_Reflection_Data.ref_Primops
let unembed_norm_step:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.norm_step =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1758 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1758 with
    | (hd1,args) ->
        let uu____1784 =
          let uu____1792 =
            let uu____1793 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1793.FStar_Syntax_Syntax.n in
          (uu____1792, args) in
        (match uu____1784 with
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
         | uu____1831 -> failwith "not an embedded norm_step")