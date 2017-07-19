open Prims
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____5 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None in
    FStar_All.pipe_right uu____5 FStar_Syntax_Syntax.fv_to_tm
let fstar_refl_embed: FStar_Syntax_Syntax.term =
  lid_as_tm FStar_Parser_Const.fstar_refl_embed_lid
let protect_embedded_term:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____18 =
        let uu____19 =
          let uu____20 = FStar_Syntax_Syntax.iarg t in
          let uu____21 =
            let uu____24 = FStar_Syntax_Syntax.as_arg x in [uu____24] in
          uu____20 :: uu____21 in
        FStar_Syntax_Syntax.mk_Tm_app fstar_refl_embed uu____19 in
      uu____18 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____31 = FStar_Syntax_Util.head_and_args t in
    match uu____31 with
    | (head1,args) ->
        let uu____80 =
          let uu____95 =
            let uu____96 = FStar_Syntax_Util.un_uinst head1 in
            uu____96.FStar_Syntax_Syntax.n in
          (uu____95, args) in
        (match uu____80 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____112::(x,uu____114)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_refl_embed_lid
             -> x
         | uu____165 ->
             let uu____180 =
               let uu____181 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____181 in
             failwith uu____180)
let embed_unit:
  Prims.unit ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun u  -> FStar_Syntax_Util.exp_unit
let unembed_unit: FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____189  -> ()
let embed_bool:
  Prims.bool ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    if b
    then FStar_Syntax_Util.exp_true_bool
    else FStar_Syntax_Util.exp_false_bool
let unembed_bool: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____199 =
      let uu____200 = FStar_Syntax_Subst.compress t in
      uu____200.FStar_Syntax_Syntax.n in
    match uu____199 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____206 -> failwith "Not an embedded bool"
let embed_int: Prims.int -> FStar_Syntax_Syntax.term =
  fun i  ->
    let uu____211 = FStar_Util.string_of_int i in
    FStar_Syntax_Util.exp_int uu____211
let unembed_int: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____216 =
      let uu____217 = FStar_Syntax_Subst.compress t in
      uu____217.FStar_Syntax_Syntax.n in
    match uu____216 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____223))
        -> FStar_Util.int_of_string s
    | uu____236 -> failwith "Not an embedded int"
let embed_string:
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
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
        (bytes,uu____252)) -> FStar_Util.string_of_unicode bytes
    | uu____257 ->
        let uu____258 =
          let uu____259 =
            let uu____260 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____260 ")" in
          Prims.strcat "Not an embedded string (" uu____259 in
        failwith uu____258
let lid_Mktuple2: FStar_Ident.lident =
  FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
    FStar_Range.dummyRange
let lid_tuple2: FStar_Ident.lident =
  FStar_Parser_Const.mk_tuple_lid (Prims.parse_int "2")
    FStar_Range.dummyRange
let embed_binder: FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term =
  fun b  ->
    FStar_Syntax_Util.mk_alien b "reflection.embed_binder"
      FStar_Pervasives_Native.None
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let uu____269 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____269 FStar_Dyn.undyn
let rec embed_list embed_a typ l =
  match l with
  | [] ->
      let uu____300 =
        let uu____301 =
          let uu____302 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____302
            [FStar_Syntax_Syntax.U_zero] in
        let uu____303 =
          let uu____304 = FStar_Syntax_Syntax.iarg typ in [uu____304] in
        FStar_Syntax_Syntax.mk_Tm_app uu____301 uu____303 in
      uu____300 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____311 =
        let uu____312 =
          let uu____313 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____313
            [FStar_Syntax_Syntax.U_zero] in
        let uu____314 =
          let uu____315 = FStar_Syntax_Syntax.iarg typ in
          let uu____316 =
            let uu____319 =
              let uu____320 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____320 in
            let uu____321 =
              let uu____324 =
                let uu____325 = embed_list embed_a typ tl1 in
                FStar_Syntax_Syntax.as_arg uu____325 in
              [uu____324] in
            uu____319 :: uu____321 in
          uu____315 :: uu____316 in
        FStar_Syntax_Syntax.mk_Tm_app uu____312 uu____314 in
      uu____311 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____351 = FStar_Syntax_Util.head_and_args l1 in
  match uu____351 with
  | (hd1,args) ->
      let uu____402 =
        let uu____417 =
          let uu____418 = FStar_Syntax_Util.un_uinst hd1 in
          uu____418.FStar_Syntax_Syntax.n in
        (uu____417, args) in
      (match uu____402 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____436) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____460)::(tl1,uu____462)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
           let uu____529 = unembed_a hd2 in
           let uu____530 = unembed_list unembed_a tl1 in uu____529 ::
             uu____530
       | uu____533 ->
           let uu____548 =
             let uu____549 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____549 in
           failwith uu____548)
let embed_binders:
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list embed_binder FStar_Reflection_Data.fstar_refl_binder l
let unembed_binders:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder Prims.list =
  fun t  -> unembed_list unembed_binder t
let embed_string_list: Prims.string Prims.list -> FStar_Syntax_Syntax.term =
  fun ss  -> embed_list embed_string FStar_TypeChecker_Common.t_string ss
let unembed_string_list: FStar_Syntax_Syntax.term -> Prims.string Prims.list
  = fun t  -> unembed_list unembed_string t
let embed_term:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> protect_embedded_term FStar_Reflection_Data.fstar_refl_term t
let unembed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t
let embed_pair embed_a t_a embed_b t_b x =
  let uu____642 =
    let uu____643 =
      let uu____644 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____644
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____645 =
      let uu____646 = FStar_Syntax_Syntax.iarg t_a in
      let uu____647 =
        let uu____650 = FStar_Syntax_Syntax.iarg t_b in
        let uu____651 =
          let uu____654 =
            let uu____655 = embed_a (FStar_Pervasives_Native.fst x) in
            FStar_Syntax_Syntax.as_arg uu____655 in
          let uu____656 =
            let uu____659 =
              let uu____660 = embed_b (FStar_Pervasives_Native.snd x) in
              FStar_Syntax_Syntax.as_arg uu____660 in
            [uu____659] in
          uu____654 :: uu____656 in
        uu____650 :: uu____651 in
      uu____646 :: uu____647 in
    FStar_Syntax_Syntax.mk_Tm_app uu____643 uu____645 in
  uu____642 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____702 = FStar_Syntax_Util.head_and_args pair in
  match uu____702 with
  | (hd1,args) ->
      let uu____755 =
        let uu____770 =
          let uu____771 = FStar_Syntax_Util.un_uinst hd1 in
          uu____771.FStar_Syntax_Syntax.n in
        (uu____770, args) in
      (match uu____755 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____791::uu____792::(a,uu____794)::(b,uu____796)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____879 = unembed_a a in
           let uu____880 = unembed_b b in (uu____879, uu____880)
       | uu____881 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | FStar_Pervasives_Native.None  ->
      let uu____930 =
        let uu____931 =
          let uu____932 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____932
            [FStar_Syntax_Syntax.U_zero] in
        let uu____933 =
          let uu____934 = FStar_Syntax_Syntax.iarg typ in [uu____934] in
        FStar_Syntax_Syntax.mk_Tm_app uu____931 uu____933 in
      uu____930 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Pervasives_Native.Some a ->
      let uu____938 =
        let uu____939 =
          let uu____940 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____940
            [FStar_Syntax_Syntax.U_zero] in
        let uu____941 =
          let uu____942 = FStar_Syntax_Syntax.iarg typ in
          let uu____943 =
            let uu____946 =
              let uu____947 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____947 in
            [uu____946] in
          uu____942 :: uu____943 in
        FStar_Syntax_Syntax.mk_Tm_app uu____939 uu____941 in
      uu____938 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____972 = FStar_Syntax_Util.head_and_args o in
  match uu____972 with
  | (hd1,args) ->
      let uu____1023 =
        let uu____1038 =
          let uu____1039 = FStar_Syntax_Util.un_uinst hd1 in
          uu____1039.FStar_Syntax_Syntax.n in
        (uu____1038, args) in
      (match uu____1023 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1057) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid ->
           FStar_Pervasives_Native.None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1079::(a,uu____1081)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid ->
           let uu____1132 = unembed_a a in
           FStar_Pervasives_Native.Some uu____1132
       | uu____1133 -> failwith "Not an embedded option")
let embed_fvar: FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  ->
    FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar"
      FStar_Pervasives_Native.None
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____1158 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____1158 FStar_Dyn.undyn
let embed_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term =
  fun env  ->
    FStar_Syntax_Util.mk_alien env "tactics_embed_env"
      FStar_Pervasives_Native.None
let unembed_env: FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env =
  fun t  ->
    let uu____1167 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____1167 FStar_Dyn.undyn
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
        let uu____1173 =
          let uu____1174 =
            let uu____1175 =
              let uu____1176 =
                let uu____1177 = FStar_Util.string_of_int i in
                FStar_Syntax_Util.exp_int uu____1177 in
              FStar_Syntax_Syntax.as_arg uu____1176 in
            [uu____1175] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____1174 in
        uu____1173 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_String s ->
        let uu____1181 =
          let uu____1182 =
            let uu____1183 =
              let uu____1184 = embed_string s in
              FStar_Syntax_Syntax.as_arg uu____1184 in
            [uu____1183] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String
            uu____1182 in
        uu____1181 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1192 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1192 with
    | (hd1,args) ->
        let uu____1241 =
          let uu____1256 =
            let uu____1257 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1257.FStar_Syntax_Syntax.n in
          (uu____1256, args) in
        (match uu____1241 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1331)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____1366 = unembed_int i in
             FStar_Reflection_Data.C_Int uu____1366
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1369)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____1404 = unembed_string s in
             FStar_Reflection_Data.C_String uu____1404
         | uu____1405 -> failwith "not an embedded vconst")
let rec embed_pattern:
  FStar_Reflection_Data.pattern ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun p  ->
    match p with
    | FStar_Reflection_Data.Pat_Constant c ->
        let uu____1425 =
          let uu____1426 =
            let uu____1427 =
              let uu____1428 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____1428 in
            [uu____1427] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant uu____1426 in
        uu____1425 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
        let uu____1437 =
          let uu____1438 =
            let uu____1439 =
              let uu____1440 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____1440 in
            let uu____1441 =
              let uu____1444 =
                let uu____1445 =
                  embed_list embed_pattern
                    FStar_Reflection_Data.fstar_refl_pattern ps in
                FStar_Syntax_Syntax.as_arg uu____1445 in
              [uu____1444] in
            uu____1439 :: uu____1441 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
            uu____1438 in
        uu____1437 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Var bv ->
        let uu____1449 =
          let uu____1450 =
            let uu____1451 =
              let uu____1452 =
                let uu____1453 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____1453 in
              FStar_Syntax_Syntax.as_arg uu____1452 in
            [uu____1451] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
            uu____1450 in
        uu____1449 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Wild bv ->
        let uu____1457 =
          let uu____1458 =
            let uu____1459 =
              let uu____1460 =
                let uu____1461 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____1461 in
              FStar_Syntax_Syntax.as_arg uu____1460 in
            [uu____1459] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____1458 in
        uu____1457 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_pattern:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.pattern =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1469 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1469 with
    | (hd1,args) ->
        let uu____1518 =
          let uu____1533 =
            let uu____1534 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1534.FStar_Syntax_Syntax.n in
          (uu____1533, args) in
        (match uu____1518 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1551)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____1586 = unembed_const c in
             FStar_Reflection_Data.Pat_Constant uu____1586
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1589)::(ps,uu____1591)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____1642 =
               let uu____1649 = unembed_fvar f in
               let uu____1650 = unembed_list unembed_pattern ps in
               (uu____1649, uu____1650) in
             FStar_Reflection_Data.Pat_Cons uu____1642
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1657)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____1692 =
               let uu____1693 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____1693 in
             FStar_Reflection_Data.Pat_Var uu____1692
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1700)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____1735 =
               let uu____1736 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____1736 in
             FStar_Reflection_Data.Pat_Wild uu____1735
         | uu____1741 -> failwith "not an embedded pattern")
let embed_branch:
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  embed_pair embed_pattern FStar_Reflection_Data.fstar_refl_pattern
    embed_term FStar_Reflection_Data.fstar_refl_term
let unembed_branch:
  FStar_Syntax_Syntax.term ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = unembed_pair unembed_pattern unembed_term
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____1775 =
          let uu____1776 =
            let uu____1777 =
              let uu____1778 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____1778 in
            [uu____1777] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____1776 in
        uu____1775 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____1782 =
          let uu____1783 =
            let uu____1784 =
              let uu____1785 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1785 in
            [uu____1784] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____1783 in
        uu____1782 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____1790 =
          let uu____1791 =
            let uu____1792 =
              let uu____1793 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____1793 in
            let uu____1794 =
              let uu____1797 =
                let uu____1798 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____1798 in
              [uu____1797] in
            uu____1792 :: uu____1794 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____1791 in
        uu____1790 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____1803 =
          let uu____1804 =
            let uu____1805 =
              let uu____1806 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1806 in
            let uu____1807 =
              let uu____1810 =
                let uu____1811 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1811 in
              [uu____1810] in
            uu____1805 :: uu____1807 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____1804 in
        uu____1803 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____1816 =
          let uu____1817 =
            let uu____1818 =
              let uu____1819 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1819 in
            let uu____1820 =
              let uu____1823 =
                let uu____1824 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1824 in
              [uu____1823] in
            uu____1818 :: uu____1820 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____1817 in
        uu____1816 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____1828 =
          let uu____1829 =
            let uu____1830 =
              let uu____1831 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____1831 in
            [uu____1830] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____1829 in
        uu____1828 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____1836 =
          let uu____1837 =
            let uu____1838 =
              let uu____1839 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1839 in
            let uu____1840 =
              let uu____1843 =
                let uu____1844 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1844 in
              [uu____1843] in
            uu____1838 :: uu____1840 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____1837 in
        uu____1836 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____1848 =
          let uu____1849 =
            let uu____1850 =
              let uu____1851 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____1851 in
            [uu____1850] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____1849 in
        uu____1848 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____1856 =
          let uu____1857 =
            let uu____1858 =
              let uu____1859 = embed_int u in
              FStar_Syntax_Syntax.as_arg uu____1859 in
            let uu____1860 =
              let uu____1863 =
                let uu____1864 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1864 in
              [uu____1863] in
            uu____1858 :: uu____1860 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____1857 in
        uu____1856 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____1873 =
          let uu____1874 =
            let uu____1875 =
              let uu____1876 = embed_term t1 in
              FStar_Syntax_Syntax.as_arg uu____1876 in
            let uu____1877 =
              let uu____1880 =
                let uu____1881 =
                  embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs in
                FStar_Syntax_Syntax.as_arg uu____1881 in
              [uu____1880] in
            uu____1875 :: uu____1877 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____1874 in
        uu____1873 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1893 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1893 with
    | (hd1,args) ->
        let uu____1942 =
          let uu____1957 =
            let uu____1958 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1958.FStar_Syntax_Syntax.n in
          (uu____1957, args) in
        (match uu____1942 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1975)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____2010 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____2010
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2013)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____2048 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____2048
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____2051)::(r,uu____2053)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____2104 =
               let uu____2109 = unembed_term l in
               let uu____2110 = unembed_term r in (uu____2109, uu____2110) in
             FStar_Reflection_Data.Tv_App uu____2104
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2113)::(t2,uu____2115)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____2166 =
               let uu____2171 = unembed_binder b in
               let uu____2172 = unembed_term t2 in (uu____2171, uu____2172) in
             FStar_Reflection_Data.Tv_Abs uu____2166
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2175)::(t2,uu____2177)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____2228 =
               let uu____2233 = unembed_binder b in
               let uu____2234 = unembed_term t2 in (uu____2233, uu____2234) in
             FStar_Reflection_Data.Tv_Arrow uu____2228
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2237)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2275)::(t2,uu____2277)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____2328 =
               let uu____2333 = unembed_binder b in
               let uu____2334 = unembed_term t2 in (uu____2333, uu____2334) in
             FStar_Reflection_Data.Tv_Refine uu____2328
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2337)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____2372 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____2372
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____2375)::(t2,uu____2377)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____2428 =
               let uu____2433 = unembed_int u in
               let uu____2434 = unembed_term t2 in (uu____2433, uu____2434) in
             FStar_Reflection_Data.Tv_Uvar uu____2428
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2437)::(brs,uu____2439)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____2490 =
               let uu____2497 = unembed_term t2 in
               let uu____2498 = unembed_list unembed_branch brs in
               (uu____2497, uu____2498) in
             FStar_Reflection_Data.Tv_Match uu____2490
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____2534 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____2563::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____2589 = init xs in x :: uu____2589
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____2600 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____2600
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____2609 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____2609
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2619) ->
        let uu____2632 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____2632
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (bs,uu____2634) ->
        FStar_Reflection_Data.C_String (FStar_Util.string_of_bytes bs)
    | uu____2639 ->
        let uu____2640 =
          let uu____2641 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____2641 in
        failwith uu____2640
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2648 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____2648
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2707 = last args in
        (match uu____2707 with
         | (a,uu____2725) ->
             let uu____2734 =
               let uu____2739 =
                 let uu____2744 =
                   let uu____2745 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2745 in
                 uu____2744 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos in
               (uu____2739, a) in
             FStar_Reflection_Data.Tv_App uu____2734)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2764,uu____2765) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____2815 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____2815 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2842 =
                    let uu____2847 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____2847) in
                  FStar_Reflection_Data.Tv_Abs uu____2842))
    | FStar_Syntax_Syntax.Tm_type uu____2852 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____2894 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____2894 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2921 =
                    let uu____2926 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____2926) in
                  FStar_Reflection_Data.Tv_Arrow uu____2921))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____2950 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____2950 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2979 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2989 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____2989
    | FStar_Syntax_Syntax.Tm_uvar (u,t2) ->
        let uu____3024 =
          let uu____3029 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____3029, t2) in
        FStar_Reflection_Data.Tv_Uvar uu____3024
    | FStar_Syntax_Syntax.Tm_match (t2,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____3093 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____3093
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____3112 =
                let uu____3119 =
                  FStar_List.map
                    (fun uu____3131  ->
                       match uu____3131 with
                       | (p1,uu____3139) -> inspect_pat p1) ps in
                (fv, uu____3119) in
              FStar_Reflection_Data.Pat_Cons uu____3112
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____3148 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___76_3202  ->
               match uu___76_3202 with
               | (pat,uu____3230,t3) ->
                   let uu____3256 = inspect_pat pat in (uu____3256, t3)) brs1 in
        FStar_Reflection_Data.Tv_Match (t2, brs2)
    | uu____3275 ->
        ((let uu____3277 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____3278 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____3277 uu____3278);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const: FStar_Reflection_Data.vconst -> FStar_Const.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____3284 =
          let uu____3295 = FStar_Util.string_of_int i in
          (uu____3295, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____3284
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string
          ((FStar_Util.bytes_of_string s), FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____3314) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____3318 =
          let uu____3329 = FStar_Syntax_Syntax.as_arg r in [uu____3329] in
        FStar_Syntax_Util.mk_app l uu____3318
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____3334 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____3334
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____3340),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____3347 =
          let uu____3352 =
            let uu____3353 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____3353 in
          FStar_Syntax_Syntax.mk uu____3352 in
        uu____3347 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        FStar_Syntax_Util.uvar_from_id u t
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____3377 =
                let uu____3378 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____3378 in
              FStar_All.pipe_left wrap uu____3377
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____3387 =
                let uu____3388 =
                  let uu____3401 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____3415 = pack_pat p1 in (uu____3415, false))
                      ps in
                  (fv, uu____3401) in
                FStar_Syntax_Syntax.Pat_cons uu____3388 in
              FStar_All.pipe_left wrap uu____3387
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___77_3465  ->
               match uu___77_3465 with
               | (pat,t1) ->
                   let uu____3484 = pack_pat pat in
                   (uu____3484, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | uu____3500 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3510 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3510 with
    | (hd1,args) ->
        let uu____3559 =
          let uu____3574 =
            let uu____3575 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3575.FStar_Syntax_Syntax.n in
          (uu____3574, args) in
        (match uu____3559 with
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
         | uu____3647 -> failwith "not an embedded order")
let order_binder:
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Reflection_Data.order
  =
  fun x  ->
    fun y  ->
      let n1 =
        FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x)
          (FStar_Pervasives_Native.fst y) in
      if n1 < (Prims.parse_int "0")
      then FStar_Reflection_Data.Lt
      else
        if n1 = (Prims.parse_int "0")
        then FStar_Reflection_Data.Eq
        else FStar_Reflection_Data.Gt
let is_free:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    fun t  -> FStar_Syntax_Util.is_free_in (FStar_Pervasives_Native.fst x) t
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
    let uu____3690 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3690 with
    | (hd1,args) ->
        let uu____3739 =
          let uu____3754 =
            let uu____3755 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3755.FStar_Syntax_Syntax.n in
          (uu____3754, args) in
        (match uu____3739 with
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
         | uu____3846 -> failwith "not an embedded norm_step")
let lookup_typ:
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list -> FStar_Reflection_Data.sigelt_view
  =
  fun env  ->
    fun ns  ->
      let lid = FStar_Parser_Const.p2l ns in
      let res = FStar_TypeChecker_Env.lookup_qname env lid in
      match res with
      | FStar_Pervasives_Native.None  -> FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____3913,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____4014,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____4031 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____4031 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____4104,n1,uu____4106) ->
                          let uu____4111 =
                            let uu____4116 = FStar_Ident.path_of_lid lid2 in
                            (uu____4116, t1) in
                          FStar_Reflection_Data.Ctor uu____4111
                      | uu____4121 -> failwith "wat 1")
                 | uu____4122 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | uu____4150 -> FStar_Reflection_Data.Unk)
let embed_ctor:
  FStar_Reflection_Data.ctor ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____4157 =
          let uu____4158 =
            let uu____4159 =
              let uu____4160 = embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____4160 in
            let uu____4161 =
              let uu____4164 =
                let uu____4165 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____4165 in
              [uu____4164] in
            uu____4159 :: uu____4161 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____4158 in
        uu____4157 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____4173 = FStar_Syntax_Util.head_and_args t1 in
    match uu____4173 with
    | (hd1,args) ->
        let uu____4222 =
          let uu____4237 =
            let uu____4238 = FStar_Syntax_Util.un_uinst hd1 in
            uu____4238.FStar_Syntax_Syntax.n in
          (uu____4237, args) in
        (match uu____4222 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4255)::(t2,uu____4257)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____4308 =
               let uu____4313 = unembed_string_list nm in
               let uu____4316 = unembed_term t2 in (uu____4313, uu____4316) in
             FStar_Reflection_Data.Ctor uu____4308
         | uu____4319 -> failwith "not an embedded ctor")
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____4350 =
          let uu____4351 =
            let uu____4352 =
              let uu____4353 = embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____4353 in
            let uu____4354 =
              let uu____4357 =
                let uu____4358 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____4358 in
              let uu____4359 =
                let uu____4362 =
                  let uu____4363 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____4363 in
                let uu____4364 =
                  let uu____4367 =
                    let uu____4368 =
                      embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____4368 in
                  [uu____4367] in
                uu____4362 :: uu____4364 in
              uu____4357 :: uu____4359 in
            uu____4352 :: uu____4354 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____4351 in
        uu____4350 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____4376 = FStar_Syntax_Util.head_and_args t1 in
    match uu____4376 with
    | (hd1,args) ->
        let uu____4425 =
          let uu____4440 =
            let uu____4441 = FStar_Syntax_Util.un_uinst hd1 in
            uu____4441.FStar_Syntax_Syntax.n in
          (uu____4440, args) in
        (match uu____4425 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4458)::(bs,uu____4460)::(t2,uu____4462)::(dcs,uu____4464)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____4547 =
               let uu____4560 = unembed_string_list nm in
               let uu____4563 = unembed_binders bs in
               let uu____4566 = unembed_term t2 in
               let uu____4567 = unembed_list unembed_ctor dcs in
               (uu____4560, uu____4563, uu____4566, uu____4567) in
             FStar_Reflection_Data.Sg_Inductive uu____4547
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____4595 -> failwith "not an embedded sigelt_view")