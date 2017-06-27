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
      let uu____218 =
        let uu____219 =
          let uu____220 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____220
            [FStar_Syntax_Syntax.U_zero] in
        let uu____221 =
          let uu____222 = FStar_Syntax_Syntax.iarg typ in [uu____222] in
        FStar_Syntax_Syntax.mk_Tm_app uu____219 uu____221 in
      uu____218 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____230 =
        let uu____231 =
          let uu____232 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____232
            [FStar_Syntax_Syntax.U_zero] in
        let uu____233 =
          let uu____234 = FStar_Syntax_Syntax.iarg typ in
          let uu____235 =
            let uu____237 =
              let uu____238 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____238 in
            let uu____239 =
              let uu____241 =
                let uu____242 = embed_list embed_a typ tl1 in
                FStar_Syntax_Syntax.as_arg uu____242 in
              [uu____241] in
            uu____237 :: uu____239 in
          uu____234 :: uu____235 in
        FStar_Syntax_Syntax.mk_Tm_app uu____231 uu____233 in
      uu____230 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____269 = FStar_Syntax_Util.head_and_args l1 in
  match uu____269 with
  | (hd1,args) ->
      let uu____296 =
        let uu____304 =
          let uu____305 = FStar_Syntax_Util.un_uinst hd1 in
          uu____305.FStar_Syntax_Syntax.n in
        (uu____304, args) in
      (match uu____296 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____315) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____329)::(tl1,uu____331)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
           let uu____365 = unembed_a hd2 in
           let uu____366 = unembed_list unembed_a tl1 in uu____365 ::
             uu____366
       | uu____368 ->
           let uu____376 =
             let uu____377 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____377 in
           failwith uu____376)
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
  let uu____459 =
    let uu____460 =
      let uu____461 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____461
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____462 =
      let uu____463 = FStar_Syntax_Syntax.iarg t_a in
      let uu____464 =
        let uu____466 = FStar_Syntax_Syntax.iarg t_b in
        let uu____467 =
          let uu____469 =
            let uu____470 = embed_a (FStar_Pervasives_Native.fst x) in
            FStar_Syntax_Syntax.as_arg uu____470 in
          let uu____471 =
            let uu____473 =
              let uu____474 = embed_b (FStar_Pervasives_Native.snd x) in
              FStar_Syntax_Syntax.as_arg uu____474 in
            [uu____473] in
          uu____469 :: uu____471 in
        uu____466 :: uu____467 in
      uu____463 :: uu____464 in
    FStar_Syntax_Syntax.mk_Tm_app uu____460 uu____462 in
  uu____459 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____516 = FStar_Syntax_Util.head_and_args pair in
  match uu____516 with
  | (hd1,args) ->
      let uu____544 =
        let uu____552 =
          let uu____553 = FStar_Syntax_Util.un_uinst hd1 in
          uu____553.FStar_Syntax_Syntax.n in
        (uu____552, args) in
      (match uu____544 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____564::uu____565::(a,uu____567)::(b,uu____569)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____611 = unembed_a a in
           let uu____612 = unembed_b b in (uu____611, uu____612)
       | uu____613 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | FStar_Pervasives_Native.None  ->
      let uu____651 =
        let uu____652 =
          let uu____653 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____653
            [FStar_Syntax_Syntax.U_zero] in
        let uu____654 =
          let uu____655 = FStar_Syntax_Syntax.iarg typ in [uu____655] in
        FStar_Syntax_Syntax.mk_Tm_app uu____652 uu____654 in
      uu____651 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Pervasives_Native.Some a ->
      let uu____661 =
        let uu____662 =
          let uu____663 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____663
            [FStar_Syntax_Syntax.U_zero] in
        let uu____664 =
          let uu____665 = FStar_Syntax_Syntax.iarg typ in
          let uu____666 =
            let uu____668 =
              let uu____669 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____669 in
            [uu____668] in
          uu____665 :: uu____666 in
        FStar_Syntax_Syntax.mk_Tm_app uu____662 uu____664 in
      uu____661 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____695 = FStar_Syntax_Util.head_and_args o in
  match uu____695 with
  | (hd1,args) ->
      let uu____722 =
        let uu____730 =
          let uu____731 = FStar_Syntax_Util.un_uinst hd1 in
          uu____731.FStar_Syntax_Syntax.n in
        (uu____730, args) in
      (match uu____722 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____741) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid ->
           FStar_Pervasives_Native.None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____753::(a,uu____755)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid ->
           let uu____781 = unembed_a a in
           FStar_Pervasives_Native.Some uu____781
       | uu____782 -> failwith "Not an embedded option")
let embed_fvar: FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  ->
    FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar"
      FStar_Pervasives_Native.None
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____799 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____799 FStar_Dyn.undyn
let embed_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term =
  fun env  ->
    FStar_Syntax_Util.mk_alien env "tactics_embed_env"
      FStar_Pervasives_Native.None
let unembed_env: FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env =
  fun t  ->
    let uu____808 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____808 FStar_Dyn.undyn
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
        let uu____814 =
          let uu____815 =
            let uu____816 =
              let uu____817 =
                let uu____818 = FStar_Util.string_of_int i in
                FStar_Syntax_Util.exp_int uu____818 in
              FStar_Syntax_Syntax.as_arg uu____817 in
            [uu____816] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____815 in
        uu____814 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
        uu____828 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____837 =
          let uu____838 =
            let uu____839 =
              let uu____840 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____840 in
            [uu____839] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____838 in
        uu____837 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
        uu____847 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
        uu____861 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
        uu____875 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____888 =
          let uu____889 =
            let uu____890 =
              let uu____891 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____891 in
            [uu____890] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____889 in
        uu____888 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
        uu____898 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____911 =
          let uu____912 =
            let uu____913 =
              let uu____914 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____914 in
            [uu____913] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____912 in
        uu____911 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____921 =
          let uu____922 =
            let uu____923 =
              let uu____924 = embed_int u in
              FStar_Syntax_Syntax.as_arg uu____924 in
            let uu____925 =
              let uu____927 =
                let uu____928 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____928 in
              [uu____927] in
            uu____923 :: uu____925 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____922 in
        uu____921 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____938 = FStar_Syntax_Util.head_and_args t1 in
    match uu____938 with
    | (hd1,args) ->
        let uu____964 =
          let uu____972 =
            let uu____973 = FStar_Syntax_Util.un_uinst hd1 in
            uu____973.FStar_Syntax_Syntax.n in
          (uu____972, args) in
        (match uu____964 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1013)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____1031 =
               let uu____1032 = FStar_Syntax_Subst.compress i in
               uu____1032.FStar_Syntax_Syntax.n in
             (match uu____1031 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____1036)) ->
                  let uu____1043 = FStar_Util.int_of_string s in
                  FStar_Reflection_Data.C_Int uu____1043
              | uu____1044 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____1045 -> failwith "not an embedded vconst")
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1058 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1058 with
    | (hd1,args) ->
        let uu____1084 =
          let uu____1092 =
            let uu____1093 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1093.FStar_Syntax_Syntax.n in
          (uu____1092, args) in
        (match uu____1084 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1103)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1121 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1121
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1124)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1142 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1142
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1145)::(r,uu____1147)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1173 =
               let uu____1176 = unembed_term l in
               let uu____1177 = unembed_term r in (uu____1176, uu____1177) in
             FStar_Reflection_Data.Tv_App uu____1173
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1180)::(t2,uu____1182)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1208 =
               let uu____1211 = unembed_binder b in
               let uu____1212 = unembed_term t2 in (uu____1211, uu____1212) in
             FStar_Reflection_Data.Tv_Abs uu____1208
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1215)::(t2,uu____1217)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1243 =
               let uu____1246 = unembed_binder b in
               let uu____1247 = unembed_term t2 in (uu____1246, uu____1247) in
             FStar_Reflection_Data.Tv_Arrow uu____1243
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1250)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1271)::(t2,uu____1273)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1299 =
               let uu____1302 = unembed_binder b in
               let uu____1303 = unembed_term t2 in (uu____1302, uu____1303) in
             FStar_Reflection_Data.Tv_Refine uu____1299
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1306)::(t2,uu____1308)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1334 =
               let uu____1337 = unembed_int u in
               let uu____1338 = unembed_term t2 in (uu____1337, uu____1338) in
             FStar_Reflection_Data.Tv_Uvar uu____1334
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1341)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1359 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1359
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1370 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1390::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1410 = init xs in x :: uu____1410
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1418 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1418
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1425 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1425
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1436 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1436
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1468 = last args in
        (match uu____1468 with
         | (a,uu____1478) ->
             let uu____1483 =
               let uu____1486 =
                 let uu____1489 =
                   let uu____1490 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1490 in
                 uu____1489 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos in
               (uu____1486, a) in
             FStar_Reflection_Data.Tv_App uu____1483)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1503,uu____1504) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1531 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1531 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1547 =
                    let uu____1550 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1550) in
                  FStar_Reflection_Data.Tv_Abs uu____1547))
    | FStar_Syntax_Syntax.Tm_type uu____1553 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1576 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1576 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1592 =
                    let uu____1595 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1595) in
                  FStar_Reflection_Data.Tv_Arrow uu____1592))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1609 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1609 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1626 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
          | FStar_Const.Const_int (s,uu____1634) ->
              let uu____1641 = FStar_Util.int_of_string s in
              FStar_Reflection_Data.C_Int uu____1641
          | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
          | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
          | uu____1642 ->
              let uu____1643 =
                let uu____1644 = FStar_Syntax_Print.const_to_string c in
                FStar_Util.format1 "unknown constant: %s" uu____1644 in
              failwith uu____1643 in
        FStar_Reflection_Data.Tv_Const c1
    | FStar_Syntax_Syntax.Tm_uvar (u,t2) ->
        let uu____1663 =
          let uu____1666 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____1666, t2) in
        FStar_Reflection_Data.Tv_Uvar uu____1663
    | uu____1669 ->
        ((let uu____1671 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1672 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1671 uu____1672);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const:
  FStar_Reflection_Data.vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Syntax_Util.exp_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____1678 = FStar_Util.string_of_int i in
        FStar_Syntax_Util.exp_int uu____1678
    | FStar_Reflection_Data.C_True  -> FStar_Syntax_Util.exp_true_bool
    | FStar_Reflection_Data.C_False  -> FStar_Syntax_Util.exp_false_bool
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1684) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1688 =
          let uu____1694 = FStar_Syntax_Syntax.as_arg r in [uu____1694] in
        FStar_Syntax_Util.mk_app l uu____1688
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1699 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1699
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1703),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c -> pack_const c
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        FStar_Syntax_Util.uvar_from_id u t
    | uu____1710 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1720 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1720 with
    | (hd1,args) ->
        let uu____1746 =
          let uu____1754 =
            let uu____1755 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1755.FStar_Syntax_Syntax.n in
          (uu____1754, args) in
        (match uu____1746 with
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
         | uu____1793 -> failwith "not an embedded order")
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
    let uu____1829 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1829 with
    | (hd1,args) ->
        let uu____1855 =
          let uu____1863 =
            let uu____1864 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1864.FStar_Syntax_Syntax.n in
          (uu____1863, args) in
        (match uu____1855 with
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
         | uu____1912 -> failwith "not an embedded norm_step")
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____1951,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____2006,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____2018 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____2018 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____2058,n1,uu____2060) ->
                          let uu____2063 =
                            let uu____2066 = FStar_Ident.path_of_lid lid2 in
                            (uu____2066, t1) in
                          FStar_Reflection_Data.Ctor uu____2063
                      | uu____2069 -> failwith "wat 1")
                 | uu____2070 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | uu____2085 -> FStar_Reflection_Data.Unk)
let embed_ctor:
  FStar_Reflection_Data.ctor ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____2092 =
          let uu____2093 =
            let uu____2094 =
              let uu____2095 = embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2095 in
            let uu____2096 =
              let uu____2098 =
                let uu____2099 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____2099 in
              [uu____2098] in
            uu____2094 :: uu____2096 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____2093 in
        uu____2092 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2109 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2109 with
    | (hd1,args) ->
        let uu____2135 =
          let uu____2143 =
            let uu____2144 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2144.FStar_Syntax_Syntax.n in
          (uu____2143, args) in
        (match uu____2135 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2154)::(t2,uu____2156)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____2182 =
               let uu____2185 = unembed_string_list nm in
               let uu____2187 = unembed_term t2 in (uu____2185, uu____2187) in
             FStar_Reflection_Data.Ctor uu____2182
         | uu____2189 -> failwith "not an embedded ctor")
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____2209 =
          let uu____2210 =
            let uu____2211 =
              let uu____2212 = embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2212 in
            let uu____2213 =
              let uu____2215 =
                let uu____2216 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____2216 in
              let uu____2217 =
                let uu____2219 =
                  let uu____2220 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____2220 in
                let uu____2221 =
                  let uu____2223 =
                    let uu____2224 =
                      embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____2224 in
                  [uu____2223] in
                uu____2219 :: uu____2221 in
              uu____2215 :: uu____2217 in
            uu____2211 :: uu____2213 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____2210 in
        uu____2209 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2234 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2234 with
    | (hd1,args) ->
        let uu____2260 =
          let uu____2268 =
            let uu____2269 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2269.FStar_Syntax_Syntax.n in
          (uu____2268, args) in
        (match uu____2260 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2279)::(bs,uu____2281)::(t2,uu____2283)::(dcs,uu____2285)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____2327 =
               let uu____2334 = unembed_string_list nm in
               let uu____2336 = unembed_binders bs in
               let uu____2338 = unembed_term t2 in
               let uu____2339 = unembed_list unembed_ctor dcs in
               (uu____2334, uu____2336, uu____2338, uu____2339) in
             FStar_Reflection_Data.Sg_Inductive uu____2327
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____2354 -> failwith "not an embedded sigelt_view")
let rec embed_pattern:
  FStar_Reflection_Data.pattern ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun p  ->
    match p with
    | FStar_Reflection_Data.Pat_Constant c ->
        let uu____2367 =
          let uu____2368 =
            let uu____2369 =
              let uu____2370 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____2370 in
            [uu____2369] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant uu____2368 in
        uu____2367 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
        let uu____2379 =
          let uu____2380 =
            let uu____2381 =
              let uu____2382 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____2382 in
            let uu____2383 =
              let uu____2385 =
                let uu____2386 =
                  embed_list embed_pattern
                    FStar_Reflection_Data.fstar_refl_pattern ps in
                FStar_Syntax_Syntax.as_arg uu____2386 in
              [uu____2385] in
            uu____2381 :: uu____2383 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
            uu____2380 in
        uu____2379 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Var bv ->
        let uu____2392 =
          let uu____2393 =
            let uu____2394 =
              let uu____2395 =
                let uu____2396 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____2396 in
              FStar_Syntax_Syntax.as_arg uu____2395 in
            [uu____2394] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
            uu____2393 in
        uu____2392 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Wild bv ->
        let uu____2402 =
          let uu____2403 =
            let uu____2404 =
              let uu____2405 =
                let uu____2406 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____2406 in
              FStar_Syntax_Syntax.as_arg uu____2405 in
            [uu____2404] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____2403 in
        uu____2402 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_pattern:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.pattern =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2416 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2416 with
    | (hd1,args) ->
        let uu____2442 =
          let uu____2450 =
            let uu____2451 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2451.FStar_Syntax_Syntax.n in
          (uu____2450, args) in
        (match uu____2442 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2461)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____2479 = unembed_const c in
             FStar_Reflection_Data.Pat_Constant uu____2479
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____2482)::(ps,uu____2484)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____2510 =
               let uu____2514 = unembed_fvar f in
               let uu____2515 = unembed_list unembed_pattern ps in
               (uu____2514, uu____2515) in
             FStar_Reflection_Data.Pat_Cons uu____2510
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2520)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____2538 =
               let uu____2539 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____2539 in
             FStar_Reflection_Data.Pat_Var uu____2538
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2544)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____2562 =
               let uu____2563 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____2563 in
             FStar_Reflection_Data.Pat_Wild uu____2562
         | uu____2566 -> failwith "not an embedded pattern")
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