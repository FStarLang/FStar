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
        (bytes,uu____147)) -> FStar_Util.string_of_unicode bytes
    | uu____150 ->
        let uu____151 =
          let uu____152 =
            let uu____153 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____153 ")" in
          Prims.strcat "Not an embedded string (" uu____152 in
        failwith uu____151
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
    let uu____158 = FStar_Syntax_Syntax.bv_to_name (fst b) in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_binder uu____158
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Syntax_Syntax.mk_binder bv
    | uu____166 -> failwith "Not an embedded binder"
let rec embed_list embed_a typ l =
  match l with
  | [] ->
      let uu____195 =
        let uu____196 =
          let uu____197 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____197
            [FStar_Syntax_Syntax.U_zero] in
        let uu____198 =
          let uu____199 = FStar_Syntax_Syntax.iarg typ in [uu____199] in
        FStar_Syntax_Syntax.mk_Tm_app uu____196 uu____198 in
      uu____195 None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____207 =
        let uu____208 =
          let uu____209 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____209
            [FStar_Syntax_Syntax.U_zero] in
        let uu____210 =
          let uu____211 = FStar_Syntax_Syntax.iarg typ in
          let uu____212 =
            let uu____214 =
              let uu____215 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____215 in
            let uu____216 =
              let uu____218 =
                let uu____219 = embed_list embed_a typ tl1 in
                FStar_Syntax_Syntax.as_arg uu____219 in
              [uu____218] in
            uu____214 :: uu____216 in
          uu____211 :: uu____212 in
        FStar_Syntax_Syntax.mk_Tm_app uu____208 uu____210 in
      uu____207 None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____246 = FStar_Syntax_Util.head_and_args l1 in
  match uu____246 with
  | (hd1,args) ->
      let uu____273 =
        let uu____281 =
          let uu____282 = FStar_Syntax_Util.un_uinst hd1 in
          uu____282.FStar_Syntax_Syntax.n in
        (uu____281, args) in
      (match uu____273 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____292) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____306)::(tl1,uu____308)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
           let uu____342 = unembed_a hd2 in
           let uu____343 = unembed_list unembed_a tl1 in uu____342 ::
             uu____343
       | uu____345 ->
           let uu____353 =
             let uu____354 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____354 in
           failwith uu____353)
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
  let uu____425 =
    let uu____426 =
      let uu____427 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____427
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____428 =
      let uu____429 = FStar_Syntax_Syntax.iarg t_a in
      let uu____430 =
        let uu____432 = FStar_Syntax_Syntax.iarg t_b in
        let uu____433 =
          let uu____435 =
            let uu____436 = embed_a (fst x) in
            FStar_Syntax_Syntax.as_arg uu____436 in
          let uu____437 =
            let uu____439 =
              let uu____440 = embed_b (snd x) in
              FStar_Syntax_Syntax.as_arg uu____440 in
            [uu____439] in
          uu____435 :: uu____437 in
        uu____432 :: uu____433 in
      uu____429 :: uu____430 in
    FStar_Syntax_Syntax.mk_Tm_app uu____426 uu____428 in
  uu____425 None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____482 = FStar_Syntax_Util.head_and_args pair in
  match uu____482 with
  | (hd1,args) ->
      let uu____510 =
        let uu____518 =
          let uu____519 = FStar_Syntax_Util.un_uinst hd1 in
          uu____519.FStar_Syntax_Syntax.n in
        (uu____518, args) in
      (match uu____510 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____530::uu____531::(a,uu____533)::(b,uu____535)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____577 = unembed_a a in
           let uu____578 = unembed_b b in (uu____577, uu____578)
       | uu____579 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | None  ->
      let uu____617 =
        let uu____618 =
          let uu____619 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____619
            [FStar_Syntax_Syntax.U_zero] in
        let uu____620 =
          let uu____621 = FStar_Syntax_Syntax.iarg typ in [uu____621] in
        FStar_Syntax_Syntax.mk_Tm_app uu____618 uu____620 in
      uu____617 None FStar_Range.dummyRange
  | Some a ->
      let uu____627 =
        let uu____628 =
          let uu____629 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____629
            [FStar_Syntax_Syntax.U_zero] in
        let uu____630 =
          let uu____631 = FStar_Syntax_Syntax.iarg typ in
          let uu____632 =
            let uu____634 =
              let uu____635 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____635 in
            [uu____634] in
          uu____631 :: uu____632 in
        FStar_Syntax_Syntax.mk_Tm_app uu____628 uu____630 in
      uu____627 None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____661 = FStar_Syntax_Util.head_and_args o in
  match uu____661 with
  | (hd1,args) ->
      let uu____688 =
        let uu____696 =
          let uu____697 = FStar_Syntax_Util.un_uinst hd1 in
          uu____697.FStar_Syntax_Syntax.n in
        (uu____696, args) in
      (match uu____688 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____707) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.none_lid ->
           None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____719::(a,uu____721)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.some_lid ->
           let uu____747 = unembed_a a in Some uu____747
       | uu____748 -> failwith "Not an embedded option")
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____761 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_fvar uu____761
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____769 -> failwith "Not an embedded fv"
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
        let uu____775 =
          let uu____776 =
            let uu____777 =
              let uu____778 = FStar_Syntax_Const.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____778 in
            [uu____777] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____776 in
        uu____775 None FStar_Range.dummyRange
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____788 =
          let uu____789 =
            let uu____790 =
              let uu____791 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____791 in
            [uu____790] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____789 in
        uu____788 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____797 =
          let uu____798 =
            let uu____799 =
              let uu____800 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____800 in
            [uu____799] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____798 in
        uu____797 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____807 =
          let uu____808 =
            let uu____809 =
              let uu____810 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____810 in
            let uu____811 =
              let uu____813 =
                let uu____814 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____814 in
              [uu____813] in
            uu____809 :: uu____811 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____808 in
        uu____807 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____821 =
          let uu____822 =
            let uu____823 =
              let uu____824 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____824 in
            let uu____825 =
              let uu____827 =
                let uu____828 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____828 in
              [uu____827] in
            uu____823 :: uu____825 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____822 in
        uu____821 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____835 =
          let uu____836 =
            let uu____837 =
              let uu____838 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____838 in
            let uu____839 =
              let uu____841 =
                let uu____842 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____842 in
              [uu____841] in
            uu____837 :: uu____839 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____836 in
        uu____835 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____848 =
          let uu____849 =
            let uu____850 =
              let uu____851 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____851 in
            [uu____850] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____849 in
        uu____848 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____858 =
          let uu____859 =
            let uu____860 =
              let uu____861 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____861 in
            let uu____862 =
              let uu____864 =
                let uu____865 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____865 in
              [uu____864] in
            uu____860 :: uu____862 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____859 in
        uu____858 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____871 =
          let uu____872 =
            let uu____873 =
              let uu____874 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____874 in
            [uu____873] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____872 in
        uu____871 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____884 = FStar_Syntax_Util.head_and_args t1 in
    match uu____884 with
    | (hd1,args) ->
        let uu____910 =
          let uu____918 =
            let uu____919 = FStar_Syntax_Util.un_uinst hd1 in
            uu____919.FStar_Syntax_Syntax.n in
          (uu____918, args) in
        (match uu____910 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____959)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____977 =
               let uu____978 = FStar_Syntax_Subst.compress i in
               uu____978.FStar_Syntax_Syntax.n in
             (match uu____977 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____982)) -> FStar_Reflection_Data.C_Int s
              | uu____989 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____990 -> failwith "not an embedded vconst")
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1003 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1003 with
    | (hd1,args) ->
        let uu____1029 =
          let uu____1037 =
            let uu____1038 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1038.FStar_Syntax_Syntax.n in
          (uu____1037, args) in
        (match uu____1029 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1048)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1066 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1066
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1069)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1087 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1087
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1090)::(r,uu____1092)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1118 =
               let uu____1121 = unembed_term l in
               let uu____1122 = unembed_term r in (uu____1121, uu____1122) in
             FStar_Reflection_Data.Tv_App uu____1118
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1125)::(t2,uu____1127)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1153 =
               let uu____1156 = unembed_binder b in
               let uu____1157 = unembed_term t2 in (uu____1156, uu____1157) in
             FStar_Reflection_Data.Tv_Abs uu____1153
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1160)::(t2,uu____1162)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1188 =
               let uu____1191 = unembed_binder b in
               let uu____1192 = unembed_term t2 in (uu____1191, uu____1192) in
             FStar_Reflection_Data.Tv_Arrow uu____1188
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1195)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1216)::(t2,uu____1218)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1244 =
               let uu____1247 = unembed_binder b in
               let uu____1248 = unembed_term t2 in (uu____1247, uu____1248) in
             FStar_Reflection_Data.Tv_Refine uu____1244
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1251)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1269 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1269
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1280 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1300::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1320 = init xs in x :: uu____1320
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1328 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1328
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1335 = FStar_Syntax_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1335
      FStar_Syntax_Syntax.Delta_equational None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (fst b)
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1346 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1346
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1378 = last args in
        (match uu____1378 with
         | (a,uu____1388) ->
             let uu____1393 =
               let uu____1396 =
                 let uu____1399 =
                   let uu____1400 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1400 in
                 uu____1399 None t1.FStar_Syntax_Syntax.pos in
               (uu____1396, a) in
             FStar_Reflection_Data.Tv_App uu____1393)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1413,uu____1414) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1461 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1461 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1477 =
                    let uu____1480 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1480) in
                  FStar_Reflection_Data.Tv_Abs uu____1477))
    | FStar_Syntax_Syntax.Tm_type uu____1483 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1506 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1506 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1522 =
                    let uu____1525 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1525) in
                  FStar_Reflection_Data.Tv_Arrow uu____1522))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1539 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1539 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1556 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
          | FStar_Const.Const_int (s,uu____1564) ->
              FStar_Reflection_Data.C_Int s
          | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
          | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
          | uu____1571 ->
              let uu____1572 =
                let uu____1573 = FStar_Syntax_Print.const_to_string c in
                FStar_Util.format1 "unknown constant: %s" uu____1573 in
              failwith uu____1572 in
        FStar_Reflection_Data.Tv_Const c1
    | uu____1574 ->
        ((let uu____1576 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1577 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1576 uu____1577);
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
    | FStar_Reflection_Data.Tv_Var (bv,uu____1588) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1592 =
          let uu____1598 = FStar_Syntax_Syntax.as_arg r in [uu____1598] in
        FStar_Syntax_Util.mk_app l uu____1592
    | FStar_Reflection_Data.Tv_Abs (b,t) -> FStar_Syntax_Util.abs [b] t None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1608 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1608
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1612),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c -> pack_const c
    | uu____1617 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1627 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1627 with
    | (hd1,args) ->
        let uu____1653 =
          let uu____1661 =
            let uu____1662 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1662.FStar_Syntax_Syntax.n in
          (uu____1661, args) in
        (match uu____1653 with
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
         | uu____1700 -> failwith "not an embedded order")
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
    let uu____1736 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1736 with
    | (hd1,args) ->
        let uu____1762 =
          let uu____1770 =
            let uu____1771 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1771.FStar_Syntax_Syntax.n in
          (uu____1770, args) in
        (match uu____1762 with
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
         | uu____1819 -> failwith "not an embedded norm_step")