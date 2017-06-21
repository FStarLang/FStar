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
let embed_term:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> protect_embedded_term FStar_Reflection_Data.fstar_refl_term t
let unembed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t
let embed_pair embed_a t_a embed_b t_b x =
  let uu____448 =
    let uu____449 =
      let uu____450 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____450
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____451 =
      let uu____452 = FStar_Syntax_Syntax.iarg t_a in
      let uu____453 =
        let uu____455 = FStar_Syntax_Syntax.iarg t_b in
        let uu____456 =
          let uu____458 =
            let uu____459 = embed_a (FStar_Pervasives_Native.fst x) in
            FStar_Syntax_Syntax.as_arg uu____459 in
          let uu____460 =
            let uu____462 =
              let uu____463 = embed_b (FStar_Pervasives_Native.snd x) in
              FStar_Syntax_Syntax.as_arg uu____463 in
            [uu____462] in
          uu____458 :: uu____460 in
        uu____455 :: uu____456 in
      uu____452 :: uu____453 in
    FStar_Syntax_Syntax.mk_Tm_app uu____449 uu____451 in
  uu____448 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____505 = FStar_Syntax_Util.head_and_args pair in
  match uu____505 with
  | (hd1,args) ->
      let uu____533 =
        let uu____541 =
          let uu____542 = FStar_Syntax_Util.un_uinst hd1 in
          uu____542.FStar_Syntax_Syntax.n in
        (uu____541, args) in
      (match uu____533 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____553::uu____554::(a,uu____556)::(b,uu____558)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____600 = unembed_a a in
           let uu____601 = unembed_b b in (uu____600, uu____601)
       | uu____602 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | FStar_Pervasives_Native.None  ->
      let uu____640 =
        let uu____641 =
          let uu____642 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____642
            [FStar_Syntax_Syntax.U_zero] in
        let uu____643 =
          let uu____644 = FStar_Syntax_Syntax.iarg typ in [uu____644] in
        FStar_Syntax_Syntax.mk_Tm_app uu____641 uu____643 in
      uu____640 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Pervasives_Native.Some a ->
      let uu____650 =
        let uu____651 =
          let uu____652 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____652
            [FStar_Syntax_Syntax.U_zero] in
        let uu____653 =
          let uu____654 = FStar_Syntax_Syntax.iarg typ in
          let uu____655 =
            let uu____657 =
              let uu____658 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____658 in
            [uu____657] in
          uu____654 :: uu____655 in
        FStar_Syntax_Syntax.mk_Tm_app uu____651 uu____653 in
      uu____650 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____684 = FStar_Syntax_Util.head_and_args o in
  match uu____684 with
  | (hd1,args) ->
      let uu____711 =
        let uu____719 =
          let uu____720 = FStar_Syntax_Util.un_uinst hd1 in
          uu____720.FStar_Syntax_Syntax.n in
        (uu____719, args) in
      (match uu____711 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____730) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid ->
           FStar_Pervasives_Native.None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____742::(a,uu____744)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid ->
           let uu____770 = unembed_a a in
           FStar_Pervasives_Native.Some uu____770
       | uu____771 -> failwith "Not an embedded option")
let embed_fvar: FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  ->
    FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar"
      FStar_Pervasives_Native.None
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____788 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____788 FStar_Dyn.undyn
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
        let uu____794 =
          let uu____795 =
            let uu____796 =
              let uu____797 =
                let uu____798 = FStar_Util.string_of_int i in
                FStar_Syntax_Util.exp_int uu____798 in
              FStar_Syntax_Syntax.as_arg uu____797 in
            [uu____796] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____795 in
        uu____794 FStar_Pervasives_Native.None FStar_Range.dummyRange
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____808 =
          let uu____809 =
            let uu____810 =
              let uu____811 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____811 in
            [uu____810] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____809 in
        uu____808 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____817 =
          let uu____818 =
            let uu____819 =
              let uu____820 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____820 in
            [uu____819] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____818 in
        uu____817 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____827 =
          let uu____828 =
            let uu____829 =
              let uu____830 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____830 in
            let uu____831 =
              let uu____833 =
                let uu____834 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____834 in
              [uu____833] in
            uu____829 :: uu____831 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____828 in
        uu____827 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____841 =
          let uu____842 =
            let uu____843 =
              let uu____844 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____844 in
            let uu____845 =
              let uu____847 =
                let uu____848 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____848 in
              [uu____847] in
            uu____843 :: uu____845 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____842 in
        uu____841 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____855 =
          let uu____856 =
            let uu____857 =
              let uu____858 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____858 in
            let uu____859 =
              let uu____861 =
                let uu____862 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____862 in
              [uu____861] in
            uu____857 :: uu____859 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____856 in
        uu____855 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____868 =
          let uu____869 =
            let uu____870 =
              let uu____871 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____871 in
            [uu____870] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____869 in
        uu____868 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____878 =
          let uu____879 =
            let uu____880 =
              let uu____881 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____881 in
            let uu____882 =
              let uu____884 =
                let uu____885 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____885 in
              [uu____884] in
            uu____880 :: uu____882 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____879 in
        uu____878 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____891 =
          let uu____892 =
            let uu____893 =
              let uu____894 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____894 in
            [uu____893] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____892 in
        uu____891 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____904 = FStar_Syntax_Util.head_and_args t1 in
    match uu____904 with
    | (hd1,args) ->
        let uu____930 =
          let uu____938 =
            let uu____939 = FStar_Syntax_Util.un_uinst hd1 in
            uu____939.FStar_Syntax_Syntax.n in
          (uu____938, args) in
        (match uu____930 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____979)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____997 =
               let uu____998 = FStar_Syntax_Subst.compress i in
               uu____998.FStar_Syntax_Syntax.n in
             (match uu____997 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____1002)) ->
                  let uu____1009 = FStar_Util.int_of_string s in
                  FStar_Reflection_Data.C_Int uu____1009
              | uu____1010 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____1011 -> failwith "not an embedded vconst")
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1024 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1024 with
    | (hd1,args) ->
        let uu____1050 =
          let uu____1058 =
            let uu____1059 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1059.FStar_Syntax_Syntax.n in
          (uu____1058, args) in
        (match uu____1050 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1069)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1087 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1087
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1090)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1108 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1108
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1111)::(r,uu____1113)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1139 =
               let uu____1142 = unembed_term l in
               let uu____1143 = unembed_term r in (uu____1142, uu____1143) in
             FStar_Reflection_Data.Tv_App uu____1139
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1146)::(t2,uu____1148)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1174 =
               let uu____1177 = unembed_binder b in
               let uu____1178 = unembed_term t2 in (uu____1177, uu____1178) in
             FStar_Reflection_Data.Tv_Abs uu____1174
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1181)::(t2,uu____1183)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1209 =
               let uu____1212 = unembed_binder b in
               let uu____1213 = unembed_term t2 in (uu____1212, uu____1213) in
             FStar_Reflection_Data.Tv_Arrow uu____1209
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1216)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1237)::(t2,uu____1239)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1265 =
               let uu____1268 = unembed_binder b in
               let uu____1269 = unembed_term t2 in (uu____1268, uu____1269) in
             FStar_Reflection_Data.Tv_Refine uu____1265
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1272)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1290 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1290
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1301 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1321::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1341 = init xs in x :: uu____1341
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1349 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1349
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1356 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1356
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1367 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1367
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1399 = last args in
        (match uu____1399 with
         | (a,uu____1409) ->
             let uu____1414 =
               let uu____1417 =
                 let uu____1420 =
                   let uu____1421 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1421 in
                 uu____1420 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos in
               (uu____1417, a) in
             FStar_Reflection_Data.Tv_App uu____1414)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1434,uu____1435) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1462 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1462 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1478 =
                    let uu____1481 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1481) in
                  FStar_Reflection_Data.Tv_Abs uu____1478))
    | FStar_Syntax_Syntax.Tm_type uu____1484 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1507 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1507 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1523 =
                    let uu____1526 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1526) in
                  FStar_Reflection_Data.Tv_Arrow uu____1523))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1540 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1540 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1557 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
          | FStar_Const.Const_int (s,uu____1565) ->
              let uu____1572 = FStar_Util.int_of_string s in
              FStar_Reflection_Data.C_Int uu____1572
          | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
          | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
          | uu____1573 ->
              let uu____1574 =
                let uu____1575 = FStar_Syntax_Print.const_to_string c in
                FStar_Util.format1 "unknown constant: %s" uu____1575 in
              failwith uu____1574 in
        FStar_Reflection_Data.Tv_Const c1
    | uu____1576 ->
        ((let uu____1578 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1579 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1578 uu____1579);
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
        let uu____1585 = FStar_Util.string_of_int i in
        FStar_Syntax_Util.exp_int uu____1585
    | FStar_Reflection_Data.C_True  -> FStar_Syntax_Util.exp_true_bool
    | FStar_Reflection_Data.C_False  -> FStar_Syntax_Util.exp_false_bool
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1591) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1595 =
          let uu____1601 = FStar_Syntax_Syntax.as_arg r in [uu____1601] in
        FStar_Syntax_Util.mk_app l uu____1595
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1606 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1606
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1610),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c -> pack_const c
    | uu____1615 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1625 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1625 with
    | (hd1,args) ->
        let uu____1651 =
          let uu____1659 =
            let uu____1660 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1660.FStar_Syntax_Syntax.n in
          (uu____1659, args) in
        (match uu____1651 with
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
         | uu____1698 -> failwith "not an embedded order")
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
    let uu____1734 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1734 with
    | (hd1,args) ->
        let uu____1760 =
          let uu____1768 =
            let uu____1769 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1769.FStar_Syntax_Syntax.n in
          (uu____1768, args) in
        (match uu____1760 with
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
         | uu____1817 -> failwith "not an embedded norm_step")