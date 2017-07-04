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
      let uu____16 =
        let uu____17 =
          let uu____18 = FStar_Syntax_Syntax.iarg t in
          let uu____19 =
            let uu____21 = FStar_Syntax_Syntax.as_arg x in [uu____21] in
          uu____18 :: uu____19 in
        FStar_Syntax_Syntax.mk_Tm_app fstar_refl_embed uu____17 in
      uu____16 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____30 = FStar_Syntax_Util.head_and_args t in
    match uu____30 with
    | (head1,args) ->
        let uu____56 =
          let uu____64 =
            let uu____65 = FStar_Syntax_Util.un_uinst head1 in
            uu____65.FStar_Syntax_Syntax.n in
          (uu____64, args) in
        (match uu____56 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____74::(x,uu____76)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_refl_embed_lid
             -> x
         | uu____102 ->
             let uu____110 =
               let uu____111 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____111 in
             failwith uu____110)
let embed_unit:
  Prims.unit ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun u  -> FStar_Syntax_Util.exp_unit
let unembed_unit: FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____119  -> ()
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
    let uu____129 =
      let uu____130 = FStar_Syntax_Subst.compress t in
      uu____130.FStar_Syntax_Syntax.n in
    match uu____129 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____134 -> failwith "Not an embedded bool"
let embed_int: Prims.int -> FStar_Syntax_Syntax.term =
  fun i  ->
    let uu____139 = FStar_Util.string_of_int i in
    FStar_Syntax_Util.exp_int uu____139
let unembed_int: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____144 =
      let uu____145 = FStar_Syntax_Subst.compress t in
      uu____145.FStar_Syntax_Syntax.n in
    match uu____144 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____149))
        -> FStar_Util.int_of_string s
    | uu____156 -> failwith "Not an embedded int"
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
        (bytes,uu____174)) -> FStar_Util.string_of_unicode bytes
    | uu____177 ->
        let uu____178 =
          let uu____179 =
            let uu____180 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____180 ")" in
          Prims.strcat "Not an embedded string (" uu____179 in
        failwith uu____178
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
    let uu____189 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____189 FStar_Dyn.undyn
let rec embed_list embed_a typ l =
  match l with
  | [] ->
      let uu____219 =
        let uu____220 =
          let uu____221 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____221
            [FStar_Syntax_Syntax.U_zero] in
        let uu____222 =
          let uu____223 = FStar_Syntax_Syntax.iarg typ in [uu____223] in
        FStar_Syntax_Syntax.mk_Tm_app uu____220 uu____222 in
      uu____219 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____231 =
        let uu____232 =
          let uu____233 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____233
            [FStar_Syntax_Syntax.U_zero] in
        let uu____234 =
          let uu____235 = FStar_Syntax_Syntax.iarg typ in
          let uu____236 =
            let uu____238 =
              let uu____239 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____239 in
            let uu____240 =
              let uu____242 =
                let uu____243 = embed_list embed_a typ tl1 in
                FStar_Syntax_Syntax.as_arg uu____243 in
              [uu____242] in
            uu____238 :: uu____240 in
          uu____235 :: uu____236 in
        FStar_Syntax_Syntax.mk_Tm_app uu____232 uu____234 in
      uu____231 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____271 = FStar_Syntax_Util.head_and_args l1 in
  match uu____271 with
  | (hd1,args) ->
      let uu____298 =
        let uu____306 =
          let uu____307 = FStar_Syntax_Util.un_uinst hd1 in
          uu____307.FStar_Syntax_Syntax.n in
        (uu____306, args) in
      (match uu____298 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____317) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____331)::(tl1,uu____333)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
           let uu____367 = unembed_a hd2 in
           let uu____368 = unembed_list unembed_a tl1 in uu____367 ::
             uu____368
       | uu____370 ->
           let uu____378 =
             let uu____379 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____379 in
           failwith uu____378)
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
  let uu____461 =
    let uu____462 =
      let uu____463 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____463
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____464 =
      let uu____465 = FStar_Syntax_Syntax.iarg t_a in
      let uu____466 =
        let uu____468 = FStar_Syntax_Syntax.iarg t_b in
        let uu____469 =
          let uu____471 =
            let uu____472 = embed_a (FStar_Pervasives_Native.fst x) in
            FStar_Syntax_Syntax.as_arg uu____472 in
          let uu____473 =
            let uu____475 =
              let uu____476 = embed_b (FStar_Pervasives_Native.snd x) in
              FStar_Syntax_Syntax.as_arg uu____476 in
            [uu____475] in
          uu____471 :: uu____473 in
        uu____468 :: uu____469 in
      uu____465 :: uu____466 in
    FStar_Syntax_Syntax.mk_Tm_app uu____462 uu____464 in
  uu____461 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____518 = FStar_Syntax_Util.head_and_args pair in
  match uu____518 with
  | (hd1,args) ->
      let uu____546 =
        let uu____554 =
          let uu____555 = FStar_Syntax_Util.un_uinst hd1 in
          uu____555.FStar_Syntax_Syntax.n in
        (uu____554, args) in
      (match uu____546 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____566::uu____567::(a,uu____569)::(b,uu____571)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____613 = unembed_a a in
           let uu____614 = unembed_b b in (uu____613, uu____614)
       | uu____615 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | FStar_Pervasives_Native.None  ->
      let uu____653 =
        let uu____654 =
          let uu____655 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____655
            [FStar_Syntax_Syntax.U_zero] in
        let uu____656 =
          let uu____657 = FStar_Syntax_Syntax.iarg typ in [uu____657] in
        FStar_Syntax_Syntax.mk_Tm_app uu____654 uu____656 in
      uu____653 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Pervasives_Native.Some a ->
      let uu____663 =
        let uu____664 =
          let uu____665 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____665
            [FStar_Syntax_Syntax.U_zero] in
        let uu____666 =
          let uu____667 = FStar_Syntax_Syntax.iarg typ in
          let uu____668 =
            let uu____670 =
              let uu____671 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____671 in
            [uu____670] in
          uu____667 :: uu____668 in
        FStar_Syntax_Syntax.mk_Tm_app uu____664 uu____666 in
      uu____663 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____697 = FStar_Syntax_Util.head_and_args o in
  match uu____697 with
  | (hd1,args) ->
      let uu____724 =
        let uu____732 =
          let uu____733 = FStar_Syntax_Util.un_uinst hd1 in
          uu____733.FStar_Syntax_Syntax.n in
        (uu____732, args) in
      (match uu____724 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____743) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid ->
           FStar_Pervasives_Native.None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____755::(a,uu____757)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid ->
           let uu____783 = unembed_a a in
           FStar_Pervasives_Native.Some uu____783
       | uu____784 -> failwith "Not an embedded option")
let embed_fvar: FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  ->
    FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar"
      FStar_Pervasives_Native.None
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____801 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____801 FStar_Dyn.undyn
let embed_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term =
  fun env  ->
    FStar_Syntax_Util.mk_alien env "tactics_embed_env"
      FStar_Pervasives_Native.None
let unembed_env: FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env =
  fun t  ->
    let uu____810 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____810 FStar_Dyn.undyn
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
        let uu____816 =
          let uu____817 =
            let uu____818 =
              let uu____819 =
                let uu____820 = FStar_Util.string_of_int i in
                FStar_Syntax_Util.exp_int uu____820 in
              FStar_Syntax_Syntax.as_arg uu____819 in
            [uu____818] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____817 in
        uu____816 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_String s ->
        let uu____826 =
          let uu____827 =
            let uu____828 =
              let uu____829 = embed_string s in
              FStar_Syntax_Syntax.as_arg uu____829 in
            [uu____828] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String
            uu____827 in
        uu____826 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____839 = FStar_Syntax_Util.head_and_args t1 in
    match uu____839 with
    | (hd1,args) ->
        let uu____865 =
          let uu____873 =
            let uu____874 = FStar_Syntax_Util.un_uinst hd1 in
            uu____874.FStar_Syntax_Syntax.n in
          (uu____873, args) in
        (match uu____865 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____914)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____932 = unembed_int i in
             FStar_Reflection_Data.C_Int uu____932
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____935)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____953 = unembed_string s in
             FStar_Reflection_Data.C_String uu____953
         | uu____954 -> failwith "not an embedded vconst")
let rec embed_pattern:
  FStar_Reflection_Data.pattern ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun p  ->
    match p with
    | FStar_Reflection_Data.Pat_Constant c ->
        let uu____967 =
          let uu____968 =
            let uu____969 =
              let uu____970 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____970 in
            [uu____969] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant uu____968 in
        uu____967 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
        let uu____979 =
          let uu____980 =
            let uu____981 =
              let uu____982 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____982 in
            let uu____983 =
              let uu____985 =
                let uu____986 =
                  embed_list embed_pattern
                    FStar_Reflection_Data.fstar_refl_pattern ps in
                FStar_Syntax_Syntax.as_arg uu____986 in
              [uu____985] in
            uu____981 :: uu____983 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
            uu____980 in
        uu____979 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Var bv ->
        let uu____992 =
          let uu____993 =
            let uu____994 =
              let uu____995 =
                let uu____996 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____996 in
              FStar_Syntax_Syntax.as_arg uu____995 in
            [uu____994] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
            uu____993 in
        uu____992 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Wild bv ->
        let uu____1002 =
          let uu____1003 =
            let uu____1004 =
              let uu____1005 =
                let uu____1006 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____1006 in
              FStar_Syntax_Syntax.as_arg uu____1005 in
            [uu____1004] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____1003 in
        uu____1002 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_pattern:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.pattern =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1016 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1016 with
    | (hd1,args) ->
        let uu____1042 =
          let uu____1050 =
            let uu____1051 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1051.FStar_Syntax_Syntax.n in
          (uu____1050, args) in
        (match uu____1042 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1061)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____1079 = unembed_const c in
             FStar_Reflection_Data.Pat_Constant uu____1079
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1082)::(ps,uu____1084)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____1110 =
               let uu____1114 = unembed_fvar f in
               let uu____1115 = unembed_list unembed_pattern ps in
               (uu____1114, uu____1115) in
             FStar_Reflection_Data.Pat_Cons uu____1110
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1120)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____1138 =
               let uu____1139 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____1139 in
             FStar_Reflection_Data.Pat_Var uu____1138
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1144)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____1162 =
               let uu____1163 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____1163 in
             FStar_Reflection_Data.Pat_Wild uu____1162
         | uu____1166 -> failwith "not an embedded pattern")
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
        let uu____1189 =
          let uu____1190 =
            let uu____1191 =
              let uu____1192 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____1192 in
            [uu____1191] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____1190 in
        uu____1189 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____1198 =
          let uu____1199 =
            let uu____1200 =
              let uu____1201 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1201 in
            [uu____1200] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____1199 in
        uu____1198 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____1208 =
          let uu____1209 =
            let uu____1210 =
              let uu____1211 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____1211 in
            let uu____1212 =
              let uu____1214 =
                let uu____1215 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____1215 in
              [uu____1214] in
            uu____1210 :: uu____1212 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____1209 in
        uu____1208 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____1222 =
          let uu____1223 =
            let uu____1224 =
              let uu____1225 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1225 in
            let uu____1226 =
              let uu____1228 =
                let uu____1229 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1229 in
              [uu____1228] in
            uu____1224 :: uu____1226 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____1223 in
        uu____1222 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____1236 =
          let uu____1237 =
            let uu____1238 =
              let uu____1239 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1239 in
            let uu____1240 =
              let uu____1242 =
                let uu____1243 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1243 in
              [uu____1242] in
            uu____1238 :: uu____1240 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____1237 in
        uu____1236 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____1249 =
          let uu____1250 =
            let uu____1251 =
              let uu____1252 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____1252 in
            [uu____1251] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____1250 in
        uu____1249 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____1259 =
          let uu____1260 =
            let uu____1261 =
              let uu____1262 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1262 in
            let uu____1263 =
              let uu____1265 =
                let uu____1266 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1266 in
              [uu____1265] in
            uu____1261 :: uu____1263 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____1260 in
        uu____1259 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____1272 =
          let uu____1273 =
            let uu____1274 =
              let uu____1275 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____1275 in
            [uu____1274] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____1273 in
        uu____1272 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____1282 =
          let uu____1283 =
            let uu____1284 =
              let uu____1285 = embed_int u in
              FStar_Syntax_Syntax.as_arg uu____1285 in
            let uu____1286 =
              let uu____1288 =
                let uu____1289 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1289 in
              [uu____1288] in
            uu____1284 :: uu____1286 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____1283 in
        uu____1282 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____1298 =
          let uu____1299 =
            let uu____1300 =
              let uu____1301 = embed_term t1 in
              FStar_Syntax_Syntax.as_arg uu____1301 in
            let uu____1302 =
              let uu____1304 =
                let uu____1305 =
                  embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs in
                FStar_Syntax_Syntax.as_arg uu____1305 in
              [uu____1304] in
            uu____1300 :: uu____1302 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____1299 in
        uu____1298 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1317 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1317 with
    | (hd1,args) ->
        let uu____1343 =
          let uu____1351 =
            let uu____1352 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1352.FStar_Syntax_Syntax.n in
          (uu____1351, args) in
        (match uu____1343 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1362)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1380 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1380
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1383)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1401 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1401
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1404)::(r,uu____1406)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1432 =
               let uu____1435 = unembed_term l in
               let uu____1436 = unembed_term r in (uu____1435, uu____1436) in
             FStar_Reflection_Data.Tv_App uu____1432
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1439)::(t2,uu____1441)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1467 =
               let uu____1470 = unembed_binder b in
               let uu____1471 = unembed_term t2 in (uu____1470, uu____1471) in
             FStar_Reflection_Data.Tv_Abs uu____1467
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1474)::(t2,uu____1476)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1502 =
               let uu____1505 = unembed_binder b in
               let uu____1506 = unembed_term t2 in (uu____1505, uu____1506) in
             FStar_Reflection_Data.Tv_Arrow uu____1502
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1509)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1530)::(t2,uu____1532)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1558 =
               let uu____1561 = unembed_binder b in
               let uu____1562 = unembed_term t2 in (uu____1561, uu____1562) in
             FStar_Reflection_Data.Tv_Refine uu____1558
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1565)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1583 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1583
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1586)::(t2,uu____1588)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1614 =
               let uu____1617 = unembed_int u in
               let uu____1618 = unembed_term t2 in (uu____1617, uu____1618) in
             FStar_Reflection_Data.Tv_Uvar uu____1614
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1621)::(brs,uu____1623)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1649 =
               let uu____1653 = unembed_term t2 in
               let uu____1654 = unembed_list unembed_branch brs in
               (uu____1653, uu____1654) in
             FStar_Reflection_Data.Tv_Match uu____1649
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1673 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1694::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1715 = init xs in x :: uu____1715
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1723 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1723
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1730 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1730
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____1740) ->
        let uu____1747 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____1747
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (bs,uu____1749) ->
        FStar_Reflection_Data.C_String (FStar_Util.string_of_bytes bs)
    | uu____1752 ->
        let uu____1753 =
          let uu____1754 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____1754 in
        failwith uu____1753
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1761 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1761
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1793 = last args in
        (match uu____1793 with
         | (a,uu____1803) ->
             let uu____1808 =
               let uu____1811 =
                 let uu____1814 =
                   let uu____1815 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1815 in
                 uu____1814 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos in
               (uu____1811, a) in
             FStar_Reflection_Data.Tv_App uu____1808)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1828,uu____1829) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1856 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1856 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1872 =
                    let uu____1875 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1875) in
                  FStar_Reflection_Data.Tv_Abs uu____1872))
    | FStar_Syntax_Syntax.Tm_type uu____1878 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1901 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1901 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1917 =
                    let uu____1920 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1920) in
                  FStar_Reflection_Data.Tv_Arrow uu____1917))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1934 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1934 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1951 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1957 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____1957
    | FStar_Syntax_Syntax.Tm_uvar (u,t2) ->
        let uu____1976 =
          let uu____1979 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____1979, t2) in
        FStar_Reflection_Data.Tv_Uvar uu____1976
    | FStar_Syntax_Syntax.Tm_match (t2,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2015 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____2015
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2026 =
                let uu____2030 =
                  FStar_List.map
                    (fun uu____2038  ->
                       match uu____2038 with
                       | (p1,uu____2043) -> inspect_pat p1) ps in
                (fv, uu____2030) in
              FStar_Reflection_Data.Pat_Cons uu____2026
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2049 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___76_2080  ->
               match uu___76_2080 with
               | (pat,uu____2095,t3) ->
                   let uu____2109 = inspect_pat pat in (uu____2109, t3)) brs1 in
        FStar_Reflection_Data.Tv_Match (t2, brs2)
    | uu____2119 ->
        ((let uu____2121 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____2122 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____2121 uu____2122);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const: FStar_Reflection_Data.vconst -> FStar_Const.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2128 =
          let uu____2134 = FStar_Util.string_of_int i in
          (uu____2134, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____2128
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string
          ((FStar_Util.bytes_of_string s), FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2147) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____2151 =
          let uu____2157 = FStar_Syntax_Syntax.as_arg r in [uu____2157] in
        FStar_Syntax_Util.mk_app l uu____2151
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____2162 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____2162
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2166),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2171 =
          let uu____2174 =
            let uu____2175 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____2175 in
          FStar_Syntax_Syntax.mk uu____2174 in
        uu____2171 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
              let uu____2200 =
                let uu____2201 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____2201 in
              FStar_All.pipe_left wrap uu____2200
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2207 =
                let uu____2208 =
                  let uu____2215 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2224 = pack_pat p1 in (uu____2224, false))
                      ps in
                  (fv, uu____2215) in
                FStar_Syntax_Syntax.Pat_cons uu____2208 in
              FStar_All.pipe_left wrap uu____2207
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___77_2253  ->
               match uu___77_2253 with
               | (pat,t1) ->
                   let uu____2264 = pack_pat pat in
                   (uu____2264, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | uu____2277 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2287 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2287 with
    | (hd1,args) ->
        let uu____2313 =
          let uu____2321 =
            let uu____2322 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2322.FStar_Syntax_Syntax.n in
          (uu____2321, args) in
        (match uu____2313 with
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
         | uu____2360 -> failwith "not an embedded order")
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
    let uu____2396 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2396 with
    | (hd1,args) ->
        let uu____2422 =
          let uu____2430 =
            let uu____2431 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2431.FStar_Syntax_Syntax.n in
          (uu____2430, args) in
        (match uu____2422 with
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
         | uu____2479 -> failwith "not an embedded norm_step")
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____2518,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____2573,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____2585 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____2585 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____2625,n1,uu____2627) ->
                          let uu____2630 =
                            let uu____2633 = FStar_Ident.path_of_lid lid2 in
                            (uu____2633, t1) in
                          FStar_Reflection_Data.Ctor uu____2630
                      | uu____2636 -> failwith "wat 1")
                 | uu____2637 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | uu____2652 -> FStar_Reflection_Data.Unk)
let embed_ctor:
  FStar_Reflection_Data.ctor ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____2659 =
          let uu____2660 =
            let uu____2661 =
              let uu____2662 = embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2662 in
            let uu____2663 =
              let uu____2665 =
                let uu____2666 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____2666 in
              [uu____2665] in
            uu____2661 :: uu____2663 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____2660 in
        uu____2659 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2676 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2676 with
    | (hd1,args) ->
        let uu____2702 =
          let uu____2710 =
            let uu____2711 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2711.FStar_Syntax_Syntax.n in
          (uu____2710, args) in
        (match uu____2702 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2721)::(t2,uu____2723)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____2749 =
               let uu____2752 = unembed_string_list nm in
               let uu____2754 = unembed_term t2 in (uu____2752, uu____2754) in
             FStar_Reflection_Data.Ctor uu____2749
         | uu____2756 -> failwith "not an embedded ctor")
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____2776 =
          let uu____2777 =
            let uu____2778 =
              let uu____2779 = embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2779 in
            let uu____2780 =
              let uu____2782 =
                let uu____2783 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____2783 in
              let uu____2784 =
                let uu____2786 =
                  let uu____2787 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____2787 in
                let uu____2788 =
                  let uu____2790 =
                    let uu____2791 =
                      embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____2791 in
                  [uu____2790] in
                uu____2786 :: uu____2788 in
              uu____2782 :: uu____2784 in
            uu____2778 :: uu____2780 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____2777 in
        uu____2776 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2801 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2801 with
    | (hd1,args) ->
        let uu____2827 =
          let uu____2835 =
            let uu____2836 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2836.FStar_Syntax_Syntax.n in
          (uu____2835, args) in
        (match uu____2827 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2846)::(bs,uu____2848)::(t2,uu____2850)::(dcs,uu____2852)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____2894 =
               let uu____2901 = unembed_string_list nm in
               let uu____2903 = unembed_binders bs in
               let uu____2905 = unembed_term t2 in
               let uu____2906 = unembed_list unembed_ctor dcs in
               (uu____2901, uu____2903, uu____2905, uu____2906) in
             FStar_Reflection_Data.Sg_Inductive uu____2894
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____2921 -> failwith "not an embedded sigelt_view")