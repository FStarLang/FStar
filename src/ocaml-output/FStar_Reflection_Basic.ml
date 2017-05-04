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
let rec embed_list embed_a t_a l =
  match l with
  | [] ->
      let uu____269 =
        let uu____270 =
          let uu____271 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____271
            [FStar_Syntax_Syntax.U_zero] in
        let uu____272 =
          let uu____273 = FStar_Syntax_Syntax.iarg t_a in [uu____273] in
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
          let uu____285 = FStar_Syntax_Syntax.iarg t_a in
          let uu____286 =
            let uu____288 =
              let uu____289 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____289 in
            let uu____290 =
              let uu____292 =
                let uu____293 = embed_list embed_a t_a tl1 in
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
let embed_env:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    let uu____439 =
      let uu____440 = FStar_TypeChecker_Env.all_binders env in
      embed_list embed_binder FStar_Reflection_Data.fstar_refl_binder
        uu____440 in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_env uu____439
let unembed_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun protected_embedded_env  ->
      let embedded_env = un_protect_embedded_term protected_embedded_env in
      let binders = unembed_list unembed_binder embedded_env in
      FStar_List.fold_left
        (fun env1  ->
           fun b  ->
             let uu____457 =
               FStar_TypeChecker_Env.try_lookup_bv env1 (Prims.fst b) in
             match uu____457 with
             | None  -> FStar_TypeChecker_Env.push_binders env1 [b]
             | uu____467 -> env1) env binders
let embed_term:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> protect_embedded_term FStar_Reflection_Data.fstar_refl_term t
let unembed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t
let embed_pair x embed_a t_a embed_b t_b =
  let uu____520 =
    let uu____521 =
      let uu____522 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____522
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____523 =
      let uu____524 = FStar_Syntax_Syntax.iarg t_a in
      let uu____525 =
        let uu____527 = FStar_Syntax_Syntax.iarg t_b in
        let uu____528 =
          let uu____530 =
            let uu____531 = embed_a (Prims.fst x) in
            FStar_Syntax_Syntax.as_arg uu____531 in
          let uu____532 =
            let uu____534 =
              let uu____535 = embed_b (Prims.snd x) in
              FStar_Syntax_Syntax.as_arg uu____535 in
            [uu____534] in
          uu____530 :: uu____532 in
        uu____527 :: uu____528 in
      uu____524 :: uu____525 in
    FStar_Syntax_Syntax.mk_Tm_app uu____521 uu____523 in
  uu____520 None FStar_Range.dummyRange
let unembed_pair pair unembed_a unembed_b =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____572 = FStar_Syntax_Util.head_and_args pair in
  match uu____572 with
  | (hd1,args) ->
      let uu____600 =
        let uu____608 =
          let uu____609 = FStar_Syntax_Util.un_uinst hd1 in
          uu____609.FStar_Syntax_Syntax.n in
        (uu____608, args) in
      (match uu____600 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____620::uu____621::(a,uu____623)::(b,uu____625)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____667 = unembed_a a in
           let uu____668 = unembed_b b in (uu____667, uu____668)
       | uu____669 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | None  ->
      let uu____703 =
        let uu____704 =
          let uu____705 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____705
            [FStar_Syntax_Syntax.U_zero] in
        let uu____706 =
          let uu____707 = FStar_Syntax_Syntax.iarg typ in [uu____707] in
        FStar_Syntax_Syntax.mk_Tm_app uu____704 uu____706 in
      uu____703 None FStar_Range.dummyRange
  | Some a ->
      let uu____713 =
        let uu____714 =
          let uu____715 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____715
            [FStar_Syntax_Syntax.U_zero] in
        let uu____716 =
          let uu____717 = FStar_Syntax_Syntax.iarg typ in
          let uu____718 =
            let uu____720 =
              let uu____721 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____721 in
            [uu____720] in
          uu____717 :: uu____718 in
        FStar_Syntax_Syntax.mk_Tm_app uu____714 uu____716 in
      uu____713 None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____744 = FStar_Syntax_Util.head_and_args o in
  match uu____744 with
  | (hd1,args) ->
      let uu____771 =
        let uu____779 =
          let uu____780 = FStar_Syntax_Util.un_uinst hd1 in
          uu____780.FStar_Syntax_Syntax.n in
        (uu____779, args) in
      (match uu____771 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____790) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.none_lid ->
           None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____802::(a,uu____804)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.some_lid ->
           let uu____830 = unembed_a a in Some uu____830
       | uu____831 -> failwith "Not an embedded option")
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____843 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_fvar uu____843
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____850 -> failwith "Not an embedded fv"
let embed_const:
  FStar_Reflection_Data.vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_Int s ->
        let uu____855 =
          let uu____856 =
            let uu____857 =
              let uu____858 = FStar_Syntax_Const.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____858 in
            [uu____857] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____856 in
        uu____855 None FStar_Range.dummyRange
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____867 =
          let uu____868 =
            let uu____869 =
              let uu____870 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____870 in
            [uu____869] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____868 in
        uu____867 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____876 =
          let uu____877 =
            let uu____878 =
              let uu____879 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____879 in
            [uu____878] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____877 in
        uu____876 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____886 =
          let uu____887 =
            let uu____888 =
              let uu____889 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____889 in
            let uu____890 =
              let uu____892 =
                let uu____893 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____893 in
              [uu____892] in
            uu____888 :: uu____890 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____887 in
        uu____886 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____900 =
          let uu____901 =
            let uu____902 =
              let uu____903 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____903 in
            let uu____904 =
              let uu____906 =
                let uu____907 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____907 in
              [uu____906] in
            uu____902 :: uu____904 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____901 in
        uu____900 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____914 =
          let uu____915 =
            let uu____916 =
              let uu____917 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____917 in
            let uu____918 =
              let uu____920 =
                let uu____921 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____921 in
              [uu____920] in
            uu____916 :: uu____918 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____915 in
        uu____914 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____927 =
          let uu____928 =
            let uu____929 =
              let uu____930 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____930 in
            [uu____929] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____928 in
        uu____927 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____937 =
          let uu____938 =
            let uu____939 =
              let uu____940 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____940 in
            let uu____941 =
              let uu____943 =
                let uu____944 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____944 in
              [uu____943] in
            uu____939 :: uu____941 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____938 in
        uu____937 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____950 =
          let uu____951 =
            let uu____952 =
              let uu____953 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____953 in
            [uu____952] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____951 in
        uu____950 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____962 = FStar_Syntax_Util.head_and_args t1 in
    match uu____962 with
    | (hd1,args) ->
        let uu____988 =
          let uu____996 =
            let uu____997 = FStar_Syntax_Util.un_uinst hd1 in
            uu____997.FStar_Syntax_Syntax.n in
          (uu____996, args) in
        (match uu____988 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit_lid
             -> FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1017)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____1035 =
               let uu____1036 = FStar_Syntax_Subst.compress i in
               uu____1036.FStar_Syntax_Syntax.n in
             (match uu____1035 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____1040)) -> FStar_Reflection_Data.C_Int s
              | uu____1047 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____1048 -> failwith "not an embedded vconst")
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1060 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1060 with
    | (hd1,args) ->
        let uu____1086 =
          let uu____1094 =
            let uu____1095 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1095.FStar_Syntax_Syntax.n in
          (uu____1094, args) in
        (match uu____1086 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1105)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1123 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1123
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1126)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1144 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1144
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1147)::(r,uu____1149)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1175 =
               let uu____1178 = unembed_term l in
               let uu____1179 = unembed_term r in (uu____1178, uu____1179) in
             FStar_Reflection_Data.Tv_App uu____1175
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1182)::(t2,uu____1184)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1210 =
               let uu____1213 = unembed_binder b in
               let uu____1214 = unembed_term t2 in (uu____1213, uu____1214) in
             FStar_Reflection_Data.Tv_Abs uu____1210
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1217)::(t2,uu____1219)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1245 =
               let uu____1248 = unembed_binder b in
               let uu____1249 = unembed_term t2 in (uu____1248, uu____1249) in
             FStar_Reflection_Data.Tv_Arrow uu____1245
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1252)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1273)::(t2,uu____1275)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1301 =
               let uu____1304 = unembed_binder b in
               let uu____1305 = unembed_term t2 in (uu____1304, uu____1305) in
             FStar_Reflection_Data.Tv_Refine uu____1301
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1308)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1326 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1326
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1337 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1355::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1373 = init xs in x :: uu____1373
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1380 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1380
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1386 = FStar_Syntax_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1386
      FStar_Syntax_Syntax.Delta_equational None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (Prims.fst b)
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let uu____1393 =
      let uu____1394 = FStar_Syntax_Subst.compress t in
      uu____1394.FStar_Syntax_Syntax.n in
    match uu____1393 with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1398 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1398
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1430 = last args in
        (match uu____1430 with
         | (a,uu____1440) ->
             let uu____1445 =
               let uu____1448 =
                 let uu____1451 =
                   let uu____1452 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1452 in
                 uu____1451 None t.FStar_Syntax_Syntax.pos in
               (uu____1448, a) in
             FStar_Reflection_Data.Tv_App uu____1445)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1465,uu____1466) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs,t1,k) ->
        let uu____1518 = FStar_Syntax_Subst.open_term (b :: bs) t1 in
        (match uu____1518 with
         | (bs',t2) ->
             let uu____1525 =
               match bs' with
               | b1::bs1 -> (b1, bs1)
               | [] -> failwith "impossible" in
             (match uu____1525 with
              | (b1,bs1) ->
                  let uu____1575 =
                    let uu____1578 = FStar_Syntax_Util.abs bs1 t2 k in
                    (b1, uu____1578) in
                  FStar_Reflection_Data.Tv_Abs uu____1575))
    | FStar_Syntax_Syntax.Tm_type uu____1581 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,k) ->
        let uu____1609 = FStar_Syntax_Subst.open_comp [b] k in
        (match uu____1609 with
         | (b',k1) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1630 -> failwith "impossible" in
             let uu____1633 =
               let uu____1636 = FStar_Syntax_Util.arrow bs k1 in
               (b1, uu____1636) in
             FStar_Reflection_Data.Tv_Arrow uu____1633)
    | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1650 = FStar_Syntax_Subst.open_term [b] t1 in
        (match uu____1650 with
         | (b',t2) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1667 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t2))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
          | FStar_Const.Const_int (s,uu____1675) ->
              FStar_Reflection_Data.C_Int s
          | uu____1682 -> failwith "unknown constant" in
        FStar_Reflection_Data.Tv_Const c1
    | uu____1683 ->
        (FStar_Util.print_string "inspect: outside of expected syntax\n";
         FStar_Reflection_Data.Tv_Unknown)
let pack:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term Prims.option =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1692) ->
        let uu____1693 = FStar_Syntax_Syntax.bv_to_tm bv in
        FStar_All.pipe_left (fun _0_28  -> Some _0_28) uu____1693
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____1696 = FStar_Syntax_Syntax.fv_to_tm fv in
        FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1696
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1700 =
          let uu____1703 =
            let uu____1709 = FStar_Syntax_Syntax.as_arg r in [uu____1709] in
          FStar_Syntax_Util.mk_app l uu____1703 in
        FStar_All.pipe_left (fun _0_30  -> Some _0_30) uu____1700
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____1719 = FStar_Syntax_Util.abs [b] t None in
        FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____1719
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1728 =
          let uu____1731 = FStar_Syntax_Syntax.mk_Total t in
          FStar_Syntax_Util.arrow [b] uu____1731 in
        FStar_All.pipe_left (fun _0_32  -> Some _0_32) uu____1728
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left (fun _0_33  -> Some _0_33)
          FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1749),t) ->
        let uu____1753 = FStar_Syntax_Util.refine bv t in
        FStar_All.pipe_left (fun _0_34  -> Some _0_34) uu____1753
    | FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Unit ) ->
        FStar_All.pipe_left (fun _0_35  -> Some _0_35)
          FStar_Syntax_Const.exp_unit
    | FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int s) ->
        let uu____1765 = FStar_Syntax_Const.exp_int s in
        FStar_All.pipe_left (fun _0_36  -> Some _0_36) uu____1765
    | uu____1767 -> None
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1775 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1775 with
    | (hd1,args) ->
        let uu____1801 =
          let uu____1809 =
            let uu____1810 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1810.FStar_Syntax_Syntax.n in
          (uu____1809, args) in
        (match uu____1801 with
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
         | uu____1848 -> failwith "not an embedded order")
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