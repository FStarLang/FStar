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
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____15 =
        let uu____16 =
          let uu____17 = FStar_Syntax_Syntax.iarg t in
          let uu____18 =
            let uu____20 = FStar_Syntax_Syntax.as_arg x in [uu____20] in
          uu____17 :: uu____18 in
        FStar_Syntax_Syntax.mk_Tm_app fstar_refl_embed uu____16 in
      uu____15 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____29 = FStar_Syntax_Util.head_and_args t in
    match uu____29 with
    | (head1,args) ->
        let uu____49 =
          let uu____56 =
            let uu____57 = FStar_Syntax_Util.un_uinst head1 in
            uu____57.FStar_Syntax_Syntax.n in
          (uu____56, args) in
        (match uu____49 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____64::(x,uu____66)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_refl_embed_lid
             -> x
         | uu____85 ->
             let uu____92 =
               let uu____93 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____93 in
             failwith uu____92)
let embed_unit:
  Prims.unit -> FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  fun u  -> FStar_Syntax_Util.exp_unit
let unembed_unit: FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____101  -> ()
let embed_bool:
  Prims.bool -> FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  fun b  ->
    if b
    then FStar_Syntax_Util.exp_true_bool
    else FStar_Syntax_Util.exp_false_bool
let unembed_bool: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____111 =
      let uu____112 = FStar_Syntax_Subst.compress t in
      uu____112.FStar_Syntax_Syntax.n in
    match uu____111 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____115 -> failwith "Not an embedded bool"
let embed_int: Prims.int -> FStar_Syntax_Syntax.term =
  fun i  ->
    let uu____120 = FStar_Util.string_of_int i in
    FStar_Syntax_Util.exp_int uu____120
let unembed_int: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____125 =
      let uu____126 = FStar_Syntax_Subst.compress t in
      uu____126.FStar_Syntax_Syntax.n in
    match uu____125 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____129))
        -> FStar_Util.int_of_string s
    | uu____136 -> failwith "Not an embedded int"
let embed_string:
  Prims.string -> FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
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
        (bytes,uu____153)) -> FStar_Util.string_of_unicode bytes
    | uu____156 ->
        let uu____157 =
          let uu____158 =
            let uu____159 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____159 ")" in
          Prims.strcat "Not an embedded string (" uu____158 in
        failwith uu____157
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
    let uu____168 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____168 FStar_Dyn.undyn
let rec embed_list embed_a typ l =
  match l with
  | [] ->
      let uu____197 =
        let uu____198 =
          let uu____199 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____199
            [FStar_Syntax_Syntax.U_zero] in
        let uu____200 =
          let uu____201 = FStar_Syntax_Syntax.iarg typ in [uu____201] in
        FStar_Syntax_Syntax.mk_Tm_app uu____198 uu____200 in
      uu____197 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____209 =
        let uu____210 =
          let uu____211 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____211
            [FStar_Syntax_Syntax.U_zero] in
        let uu____212 =
          let uu____213 = FStar_Syntax_Syntax.iarg typ in
          let uu____214 =
            let uu____216 =
              let uu____217 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____217 in
            let uu____218 =
              let uu____220 =
                let uu____221 = embed_list embed_a typ tl1 in
                FStar_Syntax_Syntax.as_arg uu____221 in
              [uu____220] in
            uu____216 :: uu____218 in
          uu____213 :: uu____214 in
        FStar_Syntax_Syntax.mk_Tm_app uu____210 uu____212 in
      uu____209 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____248 = FStar_Syntax_Util.head_and_args l1 in
  match uu____248 with
  | (hd1,args) ->
      let uu____269 =
        let uu____276 =
          let uu____277 = FStar_Syntax_Util.un_uinst hd1 in
          uu____277.FStar_Syntax_Syntax.n in
        (uu____276, args) in
      (match uu____269 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____285) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____297)::(tl1,uu____299)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
           let uu____323 = unembed_a hd2 in
           let uu____324 = unembed_list unembed_a tl1 in uu____323 ::
             uu____324
       | uu____326 ->
           let uu____333 =
             let uu____334 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____334 in
           failwith uu____333)
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
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun t  -> protect_embedded_term FStar_Reflection_Data.fstar_refl_term t
let unembed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t
let embed_pair embed_a t_a embed_b t_b x =
  let uu____416 =
    let uu____417 =
      let uu____418 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____418
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____419 =
      let uu____420 = FStar_Syntax_Syntax.iarg t_a in
      let uu____421 =
        let uu____423 = FStar_Syntax_Syntax.iarg t_b in
        let uu____424 =
          let uu____426 =
            let uu____427 = embed_a (FStar_Pervasives_Native.fst x) in
            FStar_Syntax_Syntax.as_arg uu____427 in
          let uu____428 =
            let uu____430 =
              let uu____431 = embed_b (FStar_Pervasives_Native.snd x) in
              FStar_Syntax_Syntax.as_arg uu____431 in
            [uu____430] in
          uu____426 :: uu____428 in
        uu____423 :: uu____424 in
      uu____420 :: uu____421 in
    FStar_Syntax_Syntax.mk_Tm_app uu____417 uu____419 in
  uu____416 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____473 = FStar_Syntax_Util.head_and_args pair in
  match uu____473 with
  | (hd1,args) ->
      let uu____495 =
        let uu____502 =
          let uu____503 = FStar_Syntax_Util.un_uinst hd1 in
          uu____503.FStar_Syntax_Syntax.n in
        (uu____502, args) in
      (match uu____495 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____512::uu____513::(a,uu____515)::(b,uu____517)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____547 = unembed_a a in
           let uu____548 = unembed_b b in (uu____547, uu____548)
       | uu____549 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | FStar_Pervasives_Native.None  ->
      let uu____586 =
        let uu____587 =
          let uu____588 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____588
            [FStar_Syntax_Syntax.U_zero] in
        let uu____589 =
          let uu____590 = FStar_Syntax_Syntax.iarg typ in [uu____590] in
        FStar_Syntax_Syntax.mk_Tm_app uu____587 uu____589 in
      uu____586 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Pervasives_Native.Some a ->
      let uu____596 =
        let uu____597 =
          let uu____598 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____598
            [FStar_Syntax_Syntax.U_zero] in
        let uu____599 =
          let uu____600 = FStar_Syntax_Syntax.iarg typ in
          let uu____601 =
            let uu____603 =
              let uu____604 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____604 in
            [uu____603] in
          uu____600 :: uu____601 in
        FStar_Syntax_Syntax.mk_Tm_app uu____597 uu____599 in
      uu____596 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____630 = FStar_Syntax_Util.head_and_args o in
  match uu____630 with
  | (hd1,args) ->
      let uu____651 =
        let uu____658 =
          let uu____659 = FStar_Syntax_Util.un_uinst hd1 in
          uu____659.FStar_Syntax_Syntax.n in
        (uu____658, args) in
      (match uu____651 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____667) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid ->
           FStar_Pervasives_Native.None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____677::(a,uu____679)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid ->
           let uu____698 = unembed_a a in
           FStar_Pervasives_Native.Some uu____698
       | uu____699 -> failwith "Not an embedded option")
let embed_fvar: FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  ->
    FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar"
      FStar_Pervasives_Native.None
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____715 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____715 FStar_Dyn.undyn
let embed_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term =
  fun env  ->
    FStar_Syntax_Util.mk_alien env "tactics_embed_env"
      FStar_Pervasives_Native.None
let unembed_env: FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env =
  fun t  ->
    let uu____724 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____724 FStar_Dyn.undyn
let embed_const:
  FStar_Reflection_Data.vconst ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
    | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
    | FStar_Reflection_Data.C_Int i ->
        let uu____730 =
          let uu____731 =
            let uu____732 =
              let uu____733 =
                let uu____734 = FStar_Util.string_of_int i in
                FStar_Syntax_Util.exp_int uu____734 in
              FStar_Syntax_Syntax.as_arg uu____733 in
            [uu____732] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____731 in
        uu____730 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_String s ->
        let uu____740 =
          let uu____741 =
            let uu____742 =
              let uu____743 = embed_string s in
              FStar_Syntax_Syntax.as_arg uu____743 in
            [uu____742] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String
            uu____741 in
        uu____740 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____753 = FStar_Syntax_Util.head_and_args t1 in
    match uu____753 with
    | (hd1,args) ->
        let uu____773 =
          let uu____780 =
            let uu____781 = FStar_Syntax_Util.un_uinst hd1 in
            uu____781.FStar_Syntax_Syntax.n in
          (uu____780, args) in
        (match uu____773 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____813)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____826 = unembed_int i in
             FStar_Reflection_Data.C_Int uu____826
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____829)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____842 = unembed_string s in
             FStar_Reflection_Data.C_String uu____842
         | uu____843 -> failwith "not an embedded vconst")
let rec embed_pattern:
  FStar_Reflection_Data.pattern ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun p  ->
    match p with
    | FStar_Reflection_Data.Pat_Constant c ->
        let uu____855 =
          let uu____856 =
            let uu____857 =
              let uu____858 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____858 in
            [uu____857] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant uu____856 in
        uu____855 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
        let uu____867 =
          let uu____868 =
            let uu____869 =
              let uu____870 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____870 in
            let uu____871 =
              let uu____873 =
                let uu____874 =
                  embed_list embed_pattern
                    FStar_Reflection_Data.fstar_refl_pattern ps in
                FStar_Syntax_Syntax.as_arg uu____874 in
              [uu____873] in
            uu____869 :: uu____871 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
            uu____868 in
        uu____867 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Var bv ->
        let uu____880 =
          let uu____881 =
            let uu____882 =
              let uu____883 =
                let uu____884 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____884 in
              FStar_Syntax_Syntax.as_arg uu____883 in
            [uu____882] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
            uu____881 in
        uu____880 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Wild bv ->
        let uu____890 =
          let uu____891 =
            let uu____892 =
              let uu____893 =
                let uu____894 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____894 in
              FStar_Syntax_Syntax.as_arg uu____893 in
            [uu____892] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____891 in
        uu____890 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_pattern:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.pattern =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____904 = FStar_Syntax_Util.head_and_args t1 in
    match uu____904 with
    | (hd1,args) ->
        let uu____924 =
          let uu____931 =
            let uu____932 = FStar_Syntax_Util.un_uinst hd1 in
            uu____932.FStar_Syntax_Syntax.n in
          (uu____931, args) in
        (match uu____924 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____940)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____953 = unembed_const c in
             FStar_Reflection_Data.Pat_Constant uu____953
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____956)::(ps,uu____958)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____976 =
               let uu____980 = unembed_fvar f in
               let uu____981 = unembed_list unembed_pattern ps in
               (uu____980, uu____981) in
             FStar_Reflection_Data.Pat_Cons uu____976
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____986)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____999 =
               let uu____1000 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____1000 in
             FStar_Reflection_Data.Pat_Var uu____999
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1005)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____1018 =
               let uu____1019 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____1019 in
             FStar_Reflection_Data.Pat_Wild uu____1018
         | uu____1022 -> failwith "not an embedded pattern")
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
        let uu____1044 =
          let uu____1045 =
            let uu____1046 =
              let uu____1047 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____1047 in
            [uu____1046] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____1045 in
        uu____1044 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____1053 =
          let uu____1054 =
            let uu____1055 =
              let uu____1056 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1056 in
            [uu____1055] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____1054 in
        uu____1053 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____1063 =
          let uu____1064 =
            let uu____1065 =
              let uu____1066 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____1066 in
            let uu____1067 =
              let uu____1069 =
                let uu____1070 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____1070 in
              [uu____1069] in
            uu____1065 :: uu____1067 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____1064 in
        uu____1063 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____1077 =
          let uu____1078 =
            let uu____1079 =
              let uu____1080 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1080 in
            let uu____1081 =
              let uu____1083 =
                let uu____1084 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1084 in
              [uu____1083] in
            uu____1079 :: uu____1081 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____1078 in
        uu____1077 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____1091 =
          let uu____1092 =
            let uu____1093 =
              let uu____1094 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1094 in
            let uu____1095 =
              let uu____1097 =
                let uu____1098 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1098 in
              [uu____1097] in
            uu____1093 :: uu____1095 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____1092 in
        uu____1091 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____1104 =
          let uu____1105 =
            let uu____1106 =
              let uu____1107 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____1107 in
            [uu____1106] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____1105 in
        uu____1104 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____1114 =
          let uu____1115 =
            let uu____1116 =
              let uu____1117 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1117 in
            let uu____1118 =
              let uu____1120 =
                let uu____1121 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1121 in
              [uu____1120] in
            uu____1116 :: uu____1118 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____1115 in
        uu____1114 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____1127 =
          let uu____1128 =
            let uu____1129 =
              let uu____1130 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____1130 in
            [uu____1129] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____1128 in
        uu____1127 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____1137 =
          let uu____1138 =
            let uu____1139 =
              let uu____1140 = embed_int u in
              FStar_Syntax_Syntax.as_arg uu____1140 in
            let uu____1141 =
              let uu____1143 =
                let uu____1144 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1144 in
              [uu____1143] in
            uu____1139 :: uu____1141 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____1138 in
        uu____1137 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____1153 =
          let uu____1154 =
            let uu____1155 =
              let uu____1156 = embed_term t1 in
              FStar_Syntax_Syntax.as_arg uu____1156 in
            let uu____1157 =
              let uu____1159 =
                let uu____1160 =
                  embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs in
                FStar_Syntax_Syntax.as_arg uu____1160 in
              [uu____1159] in
            uu____1155 :: uu____1157 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____1154 in
        uu____1153 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1172 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1172 with
    | (hd1,args) ->
        let uu____1192 =
          let uu____1199 =
            let uu____1200 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1200.FStar_Syntax_Syntax.n in
          (uu____1199, args) in
        (match uu____1192 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1208)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1221 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1221
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1224)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1237 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1237
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1240)::(r,uu____1242)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1260 =
               let uu____1263 = unembed_term l in
               let uu____1264 = unembed_term r in (uu____1263, uu____1264) in
             FStar_Reflection_Data.Tv_App uu____1260
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1267)::(t2,uu____1269)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1287 =
               let uu____1290 = unembed_binder b in
               let uu____1291 = unembed_term t2 in (uu____1290, uu____1291) in
             FStar_Reflection_Data.Tv_Abs uu____1287
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1294)::(t2,uu____1296)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1314 =
               let uu____1317 = unembed_binder b in
               let uu____1318 = unembed_term t2 in (uu____1317, uu____1318) in
             FStar_Reflection_Data.Tv_Arrow uu____1314
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1321)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1337)::(t2,uu____1339)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1357 =
               let uu____1360 = unembed_binder b in
               let uu____1361 = unembed_term t2 in (uu____1360, uu____1361) in
             FStar_Reflection_Data.Tv_Refine uu____1357
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1364)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1377 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1377
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1380)::(t2,uu____1382)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1400 =
               let uu____1403 = unembed_int u in
               let uu____1404 = unembed_term t2 in (uu____1403, uu____1404) in
             FStar_Reflection_Data.Tv_Uvar uu____1400
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1407)::(brs,uu____1409)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1427 =
               let uu____1431 = unembed_term t2 in
               let uu____1432 = unembed_list unembed_branch brs in
               (uu____1431, uu____1432) in
             FStar_Reflection_Data.Tv_Match uu____1427
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1449 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1468::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1488 = init xs in x :: uu____1488
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1496 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1496
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1503 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1503
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____1513) ->
        let uu____1520 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____1520
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (bs,uu____1522) ->
        FStar_Reflection_Data.C_String (FStar_Util.string_of_bytes bs)
    | uu____1525 ->
        let uu____1526 =
          let uu____1527 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____1527 in
        failwith uu____1526
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1534 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1534
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1558 = last args in
        (match uu____1558 with
         | (a,uu____1566) ->
             let uu____1569 =
               let uu____1572 =
                 let uu____1574 =
                   let uu____1575 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1575 in
                 uu____1574 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos in
               (uu____1572, a) in
             FStar_Reflection_Data.Tv_App uu____1569)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1585,uu____1586) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1609 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1609 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1625 =
                    let uu____1628 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1628) in
                  FStar_Reflection_Data.Tv_Abs uu____1625))
    | FStar_Syntax_Syntax.Tm_type uu____1631 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1650 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1650 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1666 =
                    let uu____1669 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1669) in
                  FStar_Reflection_Data.Tv_Arrow uu____1666))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1679 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1679 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1696 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1702 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____1702
    | FStar_Syntax_Syntax.Tm_uvar (u,t2) ->
        let uu____1717 =
          let uu____1720 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____1720, t2) in
        FStar_Reflection_Data.Tv_Uvar uu____1717
    | FStar_Syntax_Syntax.Tm_match (t2,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____1749 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____1749
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____1760 =
                let uu____1764 =
                  FStar_List.map
                    (fun uu____1772  ->
                       match uu____1772 with
                       | (p1,uu____1777) -> inspect_pat p1) ps in
                (fv, uu____1764) in
              FStar_Reflection_Data.Pat_Cons uu____1760
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____1783 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___76_1809  ->
               match uu___76_1809 with
               | (pat,uu____1821,t3) ->
                   let uu____1831 = inspect_pat pat in (uu____1831, t3)) brs1 in
        FStar_Reflection_Data.Tv_Match (t2, brs2)
    | uu____1838 ->
        ((let uu____1840 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1841 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1840 uu____1841);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const: FStar_Reflection_Data.vconst -> FStar_Const.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____1847 =
          let uu____1853 = FStar_Util.string_of_int i in
          (uu____1853, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____1847
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string
          ((FStar_Util.bytes_of_string s), FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1866) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1870 =
          let uu____1875 = FStar_Syntax_Syntax.as_arg r in [uu____1875] in
        FStar_Syntax_Util.mk_app l uu____1870
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1880 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1880
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1883),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____1888 =
          let uu____1890 =
            let uu____1891 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____1891 in
          FStar_Syntax_Syntax.mk uu____1890 in
        uu____1888 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
              let uu____1914 =
                let uu____1915 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____1915 in
              FStar_All.pipe_left wrap uu____1914
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____1921 =
                let uu____1922 =
                  let uu____1929 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____1938 = pack_pat p1 in (uu____1938, false))
                      ps in
                  (fv, uu____1929) in
                FStar_Syntax_Syntax.Pat_cons uu____1922 in
              FStar_All.pipe_left wrap uu____1921
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___77_1965  ->
               match uu___77_1965 with
               | (pat,t1) ->
                   let uu____1975 = pack_pat pat in
                   (uu____1975, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | uu____1985 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1995 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1995 with
    | (hd1,args) ->
        let uu____2015 =
          let uu____2022 =
            let uu____2023 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2023.FStar_Syntax_Syntax.n in
          (uu____2022, args) in
        (match uu____2015 with
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
         | uu____2053 -> failwith "not an embedded order")
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
    let uu____2088 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2088 with
    | (hd1,args) ->
        let uu____2108 =
          let uu____2115 =
            let uu____2116 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2116.FStar_Syntax_Syntax.n in
          (uu____2115, args) in
        (match uu____2108 with
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
         | uu____2154 -> failwith "not an embedded norm_step")
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____2192,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____2247,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____2259 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____2259 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____2299,n1,uu____2301) ->
                          let uu____2304 =
                            let uu____2307 = FStar_Ident.path_of_lid lid2 in
                            (uu____2307, t1) in
                          FStar_Reflection_Data.Ctor uu____2304
                      | uu____2310 -> failwith "wat 1")
                 | uu____2311 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | uu____2326 -> FStar_Reflection_Data.Unk)
let embed_ctor:
  FStar_Reflection_Data.ctor ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____2333 =
          let uu____2334 =
            let uu____2335 =
              let uu____2336 = embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2336 in
            let uu____2337 =
              let uu____2339 =
                let uu____2340 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____2340 in
              [uu____2339] in
            uu____2335 :: uu____2337 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____2334 in
        uu____2333 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2350 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2350 with
    | (hd1,args) ->
        let uu____2370 =
          let uu____2377 =
            let uu____2378 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2378.FStar_Syntax_Syntax.n in
          (uu____2377, args) in
        (match uu____2370 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2386)::(t2,uu____2388)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____2406 =
               let uu____2409 = unembed_string_list nm in
               let uu____2411 = unembed_term t2 in (uu____2409, uu____2411) in
             FStar_Reflection_Data.Ctor uu____2406
         | uu____2413 -> failwith "not an embedded ctor")
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____2432 =
          let uu____2433 =
            let uu____2434 =
              let uu____2435 = embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2435 in
            let uu____2436 =
              let uu____2438 =
                let uu____2439 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____2439 in
              let uu____2440 =
                let uu____2442 =
                  let uu____2443 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____2443 in
                let uu____2444 =
                  let uu____2446 =
                    let uu____2447 =
                      embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____2447 in
                  [uu____2446] in
                uu____2442 :: uu____2444 in
              uu____2438 :: uu____2440 in
            uu____2434 :: uu____2436 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____2433 in
        uu____2432 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2457 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2457 with
    | (hd1,args) ->
        let uu____2477 =
          let uu____2484 =
            let uu____2485 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2485.FStar_Syntax_Syntax.n in
          (uu____2484, args) in
        (match uu____2477 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2493)::(bs,uu____2495)::(t2,uu____2497)::(dcs,uu____2499)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____2527 =
               let uu____2534 = unembed_string_list nm in
               let uu____2536 = unembed_binders bs in
               let uu____2538 = unembed_term t2 in
               let uu____2539 = unembed_list unembed_ctor dcs in
               (uu____2534, uu____2536, uu____2538, uu____2539) in
             FStar_Reflection_Data.Sg_Inductive uu____2527
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____2552 -> failwith "not an embedded sigelt_view")