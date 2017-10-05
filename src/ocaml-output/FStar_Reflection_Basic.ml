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
      let uu____16 =
        let uu____17 =
          let uu____18 = FStar_Syntax_Syntax.iarg t in
          let uu____19 =
            let uu____22 = FStar_Syntax_Syntax.as_arg x in [uu____22] in
          uu____18 :: uu____19 in
        FStar_Syntax_Syntax.mk_Tm_app fstar_refl_embed uu____17 in
      uu____16 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____29 = FStar_Syntax_Util.head_and_args t in
    match uu____29 with
    | (head1,args) ->
        let uu____66 =
          let uu____79 =
            let uu____80 = FStar_Syntax_Util.un_uinst head1 in
            uu____80.FStar_Syntax_Syntax.n in
          (uu____79, args) in
        (match uu____66 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____92::(x,uu____94)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_refl_embed_lid
             -> x
         | uu____131 ->
             let uu____144 =
               let uu____145 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____145 in
             failwith uu____144)
let embed_binder: FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term =
  fun b  ->
    FStar_Syntax_Util.mk_alien b "reflection.embed_binder"
      FStar_Pervasives_Native.None
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let uu____154 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____154 FStar_Dyn.undyn
let embed_binders:
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  ->
    FStar_Syntax_Embeddings.embed_list embed_binder
      FStar_Reflection_Data.fstar_refl_binder l
let unembed_binders:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder Prims.list =
  fun t  -> FStar_Syntax_Embeddings.unembed_list unembed_binder t
let embed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> protect_embedded_term FStar_Syntax_Syntax.tun t
let unembed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t
let embed_fvar: FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  ->
    FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar"
      FStar_Pervasives_Native.None
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____185 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____185 FStar_Dyn.undyn
let embed_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term =
  fun env  ->
    FStar_Syntax_Util.mk_alien env "tactics_embed_env"
      FStar_Pervasives_Native.None
let unembed_env: FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env =
  fun t  ->
    let uu____194 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____194 FStar_Dyn.undyn
let embed_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
    | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
    | FStar_Reflection_Data.C_Int i ->
        let uu____200 =
          let uu____201 =
            let uu____202 =
              let uu____203 =
                let uu____204 = FStar_Util.string_of_int i in
                FStar_Syntax_Util.exp_int uu____204 in
              FStar_Syntax_Syntax.as_arg uu____203 in
            [uu____202] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____201 in
        uu____200 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_String s ->
        let uu____208 =
          let uu____209 =
            let uu____210 =
              let uu____211 = FStar_Syntax_Embeddings.embed_string s in
              FStar_Syntax_Syntax.as_arg uu____211 in
            [uu____210] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String
            uu____209 in
        uu____208 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____219 = FStar_Syntax_Util.head_and_args t1 in
    match uu____219 with
    | (hd1,args) ->
        let uu____256 =
          let uu____269 =
            let uu____270 = FStar_Syntax_Util.un_uinst hd1 in
            uu____270.FStar_Syntax_Syntax.n in
          (uu____269, args) in
        (match uu____256 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____328)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____353 = FStar_Syntax_Embeddings.unembed_int i in
             FStar_Reflection_Data.C_Int uu____353
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____356)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____381 = FStar_Syntax_Embeddings.unembed_string s in
             FStar_Reflection_Data.C_String uu____381
         | uu____382 -> failwith "not an embedded vconst")
let rec embed_pattern:
  FStar_Reflection_Data.pattern -> FStar_Syntax_Syntax.term =
  fun p  ->
    match p with
    | FStar_Reflection_Data.Pat_Constant c ->
        let uu____400 =
          let uu____401 =
            let uu____402 =
              let uu____403 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____403 in
            [uu____402] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant uu____401 in
        uu____400 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
        let uu____412 =
          let uu____413 =
            let uu____414 =
              let uu____415 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____415 in
            let uu____416 =
              let uu____419 =
                let uu____420 =
                  FStar_Syntax_Embeddings.embed_list embed_pattern
                    FStar_Reflection_Data.fstar_refl_pattern ps in
                FStar_Syntax_Syntax.as_arg uu____420 in
              [uu____419] in
            uu____414 :: uu____416 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
            uu____413 in
        uu____412 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Var bv ->
        let uu____424 =
          let uu____425 =
            let uu____426 =
              let uu____427 =
                let uu____428 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____428 in
              FStar_Syntax_Syntax.as_arg uu____427 in
            [uu____426] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
            uu____425 in
        uu____424 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Wild bv ->
        let uu____432 =
          let uu____433 =
            let uu____434 =
              let uu____435 =
                let uu____436 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____436 in
              FStar_Syntax_Syntax.as_arg uu____435 in
            [uu____434] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____433 in
        uu____432 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_pattern:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.pattern =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____444 = FStar_Syntax_Util.head_and_args t1 in
    match uu____444 with
    | (hd1,args) ->
        let uu____481 =
          let uu____494 =
            let uu____495 = FStar_Syntax_Util.un_uinst hd1 in
            uu____495.FStar_Syntax_Syntax.n in
          (uu____494, args) in
        (match uu____481 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____508)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____533 = unembed_const c in
             FStar_Reflection_Data.Pat_Constant uu____533
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____536)::(ps,uu____538)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____573 =
               let uu____580 = unembed_fvar f in
               let uu____581 =
                 FStar_Syntax_Embeddings.unembed_list unembed_pattern ps in
               (uu____580, uu____581) in
             FStar_Reflection_Data.Pat_Cons uu____573
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____588)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____613 =
               let uu____614 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____614 in
             FStar_Reflection_Data.Pat_Var uu____613
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____621)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____646 =
               let uu____647 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____647 in
             FStar_Reflection_Data.Pat_Wild uu____646
         | uu____652 -> failwith "not an embedded pattern")
let embed_branch:
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  FStar_Syntax_Embeddings.embed_pair embed_pattern
    FStar_Reflection_Data.fstar_refl_pattern embed_term
    FStar_Reflection_Data.fstar_refl_term
let unembed_branch:
  FStar_Syntax_Syntax.term ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = FStar_Syntax_Embeddings.unembed_pair unembed_pattern unembed_term
let embed_aqualv: FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.term =
  fun q  ->
    match q with
    | FStar_Reflection_Data.Q_Explicit  ->
        FStar_Reflection_Data.ref_Q_Explicit
    | FStar_Reflection_Data.Q_Implicit  ->
        FStar_Reflection_Data.ref_Q_Implicit
let unembed_aqualv: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.aqualv
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____688 = FStar_Syntax_Util.head_and_args t1 in
    match uu____688 with
    | (hd1,args) ->
        let uu____725 =
          let uu____738 =
            let uu____739 = FStar_Syntax_Util.un_uinst hd1 in
            uu____739.FStar_Syntax_Syntax.n in
          (uu____738, args) in
        (match uu____725 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit_lid
             -> FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit_lid
             -> FStar_Reflection_Data.Q_Implicit
         | uu____780 -> failwith "not an embedded aqualv")
let embed_argv:
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  FStar_Syntax_Embeddings.embed_pair embed_term
    FStar_Reflection_Data.fstar_refl_term embed_aqualv
    FStar_Reflection_Data.fstar_refl_aqualv
let unembed_argv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2
  = FStar_Syntax_Embeddings.unembed_pair unembed_term unembed_aqualv
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____812 =
          let uu____813 =
            let uu____814 =
              let uu____815 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____815 in
            [uu____814] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____813 in
        uu____812 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____819 =
          let uu____820 =
            let uu____821 =
              let uu____822 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____822 in
            [uu____821] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____820 in
        uu____819 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____827 =
          let uu____828 =
            let uu____829 =
              let uu____830 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____830 in
            let uu____831 =
              let uu____834 =
                let uu____835 = embed_argv a in
                FStar_Syntax_Syntax.as_arg uu____835 in
              [uu____834] in
            uu____829 :: uu____831 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____828 in
        uu____827 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____840 =
          let uu____841 =
            let uu____842 =
              let uu____843 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____843 in
            let uu____844 =
              let uu____847 =
                let uu____848 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____848 in
              [uu____847] in
            uu____842 :: uu____844 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____841 in
        uu____840 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____853 =
          let uu____854 =
            let uu____855 =
              let uu____856 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____856 in
            let uu____857 =
              let uu____860 =
                let uu____861 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____861 in
              [uu____860] in
            uu____855 :: uu____857 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____854 in
        uu____853 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____865 =
          let uu____866 =
            let uu____867 =
              let uu____868 = FStar_Syntax_Embeddings.embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____868 in
            [uu____867] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____866 in
        uu____865 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____873 =
          let uu____874 =
            let uu____875 =
              let uu____876 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____876 in
            let uu____877 =
              let uu____880 =
                let uu____881 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____881 in
              [uu____880] in
            uu____875 :: uu____877 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____874 in
        uu____873 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____885 =
          let uu____886 =
            let uu____887 =
              let uu____888 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____888 in
            [uu____887] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____886 in
        uu____885 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____893 =
          let uu____894 =
            let uu____895 =
              let uu____896 = FStar_Syntax_Embeddings.embed_int u in
              FStar_Syntax_Syntax.as_arg uu____896 in
            let uu____897 =
              let uu____900 =
                let uu____901 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____901 in
              [uu____900] in
            uu____895 :: uu____897 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____894 in
        uu____893 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let uu____907 =
          let uu____908 =
            let uu____909 =
              let uu____910 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____910 in
            let uu____911 =
              let uu____914 =
                let uu____915 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____915 in
              let uu____916 =
                let uu____919 =
                  let uu____920 = embed_term t2 in
                  FStar_Syntax_Syntax.as_arg uu____920 in
                [uu____919] in
              uu____914 :: uu____916 in
            uu____909 :: uu____911 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let
            uu____908 in
        uu____907 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____929 =
          let uu____930 =
            let uu____931 =
              let uu____932 = embed_term t1 in
              FStar_Syntax_Syntax.as_arg uu____932 in
            let uu____933 =
              let uu____936 =
                let uu____937 =
                  FStar_Syntax_Embeddings.embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs in
                FStar_Syntax_Syntax.as_arg uu____937 in
              [uu____936] in
            uu____931 :: uu____933 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____930 in
        uu____929 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____949 = FStar_Syntax_Util.head_and_args t1 in
    match uu____949 with
    | (hd1,args) ->
        let uu____986 =
          let uu____999 =
            let uu____1000 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1000.FStar_Syntax_Syntax.n in
          (uu____999, args) in
        (match uu____986 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1013)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1038 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1038
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1041)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1066 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1066
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1069)::(r,uu____1071)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1106 =
               let uu____1111 = unembed_term l in
               let uu____1112 = unembed_argv r in (uu____1111, uu____1112) in
             FStar_Reflection_Data.Tv_App uu____1106
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1123)::(t2,uu____1125)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1160 =
               let uu____1165 = unembed_binder b in
               let uu____1166 = unembed_term t2 in (uu____1165, uu____1166) in
             FStar_Reflection_Data.Tv_Abs uu____1160
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1169)::(t2,uu____1171)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1206 =
               let uu____1211 = unembed_binder b in
               let uu____1212 = unembed_term t2 in (uu____1211, uu____1212) in
             FStar_Reflection_Data.Tv_Arrow uu____1206
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1215)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             (FStar_Syntax_Embeddings.unembed_unit u;
              FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1243)::(t2,uu____1245)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1280 =
               let uu____1285 = unembed_binder b in
               let uu____1286 = unembed_term t2 in (uu____1285, uu____1286) in
             FStar_Reflection_Data.Tv_Refine uu____1280
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1289)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1314 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1314
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1317)::(t2,uu____1319)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1354 =
               let uu____1359 = FStar_Syntax_Embeddings.unembed_int u in
               let uu____1360 = unembed_term t2 in (uu____1359, uu____1360) in
             FStar_Reflection_Data.Tv_Uvar uu____1354
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1363)::(t11,uu____1365)::(t2,uu____1367)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let_lid
             ->
             let uu____1412 =
               let uu____1419 = unembed_binder b in
               let uu____1420 = unembed_term t11 in
               let uu____1421 = unembed_term t2 in
               (uu____1419, uu____1420, uu____1421) in
             FStar_Reflection_Data.Tv_Let uu____1412
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1424)::(brs,uu____1426)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1461 =
               let uu____1468 = unembed_term t2 in
               let uu____1469 =
                 FStar_Syntax_Embeddings.unembed_list unembed_branch brs in
               (uu____1468, uu____1469) in
             FStar_Reflection_Data.Tv_Match uu____1461
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1501 -> failwith "not an embedded term_view")
let rec last: 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____1528::xs -> last xs
let rec init: 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____1554 = init xs in x :: uu____1554
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1565 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1565
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1574 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1574
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____1584) ->
        let uu____1597 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____1597
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____1599) ->
        FStar_Reflection_Data.C_String s
    | uu____1600 ->
        let uu____1601 =
          let uu____1602 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____1602 in
        failwith uu____1601
let rec inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let t2 = FStar_Syntax_Util.un_uinst t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____1610) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1616 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1616
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1659 = last args in
        (match uu____1659 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____1679) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit in
             let uu____1680 =
               let uu____1685 =
                 let uu____1688 =
                   let uu____1689 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1689 in
                 uu____1688 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos in
               (uu____1685, (a, q')) in
             FStar_Reflection_Data.Tv_App uu____1680)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1708,uu____1709) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____1751 = FStar_Syntax_Subst.open_term bs t3 in
        (match uu____1751 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1778 =
                    let uu____1783 = FStar_Syntax_Util.abs bs2 t4 k in
                    (b, uu____1783) in
                  FStar_Reflection_Data.Tv_Abs uu____1778))
    | FStar_Syntax_Syntax.Tm_type uu____1788 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1822 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1822 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1849 =
                    let uu____1854 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1854) in
                  FStar_Reflection_Data.Tv_Arrow uu____1849))
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1870 = FStar_Syntax_Subst.open_term [b] t3 in
        (match uu____1870 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1899 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1909 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____1909
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____1936 =
          let uu____1941 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____1941, t3) in
        FStar_Reflection_Data.Tv_Uvar uu____1936
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____1961 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____1964 = FStar_Syntax_Subst.open_term [b] t21 in
               (match uu____1964 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____1993 ->
                          failwith
                            "impossible: open_term returned different amount of binders" in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2051 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____2051
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2070 =
                let uu____2077 =
                  FStar_List.map
                    (fun uu____2089  ->
                       match uu____2089 with
                       | (p1,uu____2097) -> inspect_pat p1) ps in
                (fv, uu____2077) in
              FStar_Reflection_Data.Pat_Cons uu____2070
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2106 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___104_2150  ->
               match uu___104_2150 with
               | (pat,uu____2172,t4) ->
                   let uu____2190 = inspect_pat pat in (uu____2190, t4)) brs1 in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2203 ->
        ((let uu____2205 = FStar_Syntax_Print.tag_of_term t2 in
          let uu____2206 = FStar_Syntax_Print.term_to_string t2 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____2205 uu____2206);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2212 =
          let uu____2223 = FStar_Util.string_of_int i in
          (uu____2223, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____2212
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2240) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2249 =
               let uu____2258 = FStar_Syntax_Syntax.as_arg r in [uu____2258] in
             FStar_Syntax_Util.mk_app l uu____2249
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2259 =
               let uu____2268 = FStar_Syntax_Syntax.iarg r in [uu____2268] in
             FStar_Syntax_Util.mk_app l uu____2259)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____2273 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____2273
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2277),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2284 =
          let uu____2287 =
            let uu____2288 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____2288 in
          FStar_Syntax_Syntax.mk uu____2287 in
        uu____2284 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        FStar_Syntax_Util.uvar_from_id u t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 in
        let uu____2299 =
          let uu____2302 =
            let uu____2303 =
              let uu____2316 = FStar_Syntax_Subst.close [b] t2 in
              ((false, [lb]), uu____2316) in
            FStar_Syntax_Syntax.Tm_let uu____2303 in
          FStar_Syntax_Syntax.mk uu____2302 in
        uu____2299 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2345 =
                let uu____2346 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____2346 in
              FStar_All.pipe_left wrap uu____2345
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2355 =
                let uu____2356 =
                  let uu____2369 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2383 = pack_pat p1 in (uu____2383, false))
                      ps in
                  (fv, uu____2369) in
                FStar_Syntax_Syntax.Pat_cons uu____2356 in
              FStar_All.pipe_left wrap uu____2355
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___105_2429  ->
               match uu___105_2429 with
               | (pat,t1) ->
                   let uu____2446 = pack_pat pat in
                   (uu____2446, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | uu____2458 -> failwith "pack: unexpected term view"
let embed_order: FStar_Order.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Order.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2468 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2468 with
    | (hd1,args) ->
        let uu____2505 =
          let uu____2518 =
            let uu____2519 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2519.FStar_Syntax_Syntax.n in
          (uu____2518, args) in
        (match uu____2505 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Lt_lid
             -> FStar_Order.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Eq_lid
             -> FStar_Order.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Gt_lid
             -> FStar_Order.Gt
         | uu____2575 -> failwith "not an embedded order")
let compare_binder:
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Order.order
  =
  fun x  ->
    fun y  ->
      let n1 =
        FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x)
          (FStar_Pervasives_Native.fst y) in
      if n1 < (Prims.parse_int "0")
      then FStar_Order.Lt
      else
        if n1 = (Prims.parse_int "0") then FStar_Order.Eq else FStar_Order.Gt
let is_free:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    fun t  -> FStar_Syntax_Util.is_free_in (FStar_Pervasives_Native.fst x) t
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____2659,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____2760,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____2777 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____2777 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____2850,n1,uu____2852) ->
                          let uu____2857 =
                            let uu____2862 = FStar_Ident.path_of_lid lid2 in
                            (uu____2862, t1) in
                          FStar_Reflection_Data.Ctor uu____2857
                      | uu____2867 -> failwith "wat 1")
                 | uu____2868 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2897) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____2912 ->
                     failwith "global Sig_let has bv" in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____2917 -> FStar_Reflection_Data.Unk)
let embed_ctor: FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____2924 =
          let uu____2925 =
            let uu____2926 =
              let uu____2927 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2927 in
            let uu____2928 =
              let uu____2931 =
                let uu____2932 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____2932 in
              [uu____2931] in
            uu____2926 :: uu____2928 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____2925 in
        uu____2924 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2940 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2940 with
    | (hd1,args) ->
        let uu____2977 =
          let uu____2990 =
            let uu____2991 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2991.FStar_Syntax_Syntax.n in
          (uu____2990, args) in
        (match uu____2977 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3004)::(t2,uu____3006)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3041 =
               let uu____3046 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____3049 = unembed_term t2 in (uu____3046, uu____3049) in
             FStar_Reflection_Data.Ctor uu____3041
         | uu____3052 -> failwith "not an embedded ctor")
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3081 =
          let uu____3082 =
            let uu____3083 =
              let uu____3084 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____3084 in
            let uu____3085 =
              let uu____3088 =
                let uu____3089 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____3089 in
              let uu____3090 =
                let uu____3093 =
                  let uu____3094 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____3094 in
                let uu____3095 =
                  let uu____3098 =
                    let uu____3099 =
                      FStar_Syntax_Embeddings.embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____3099 in
                  [uu____3098] in
                uu____3093 :: uu____3095 in
              uu____3088 :: uu____3090 in
            uu____3083 :: uu____3085 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____3082 in
        uu____3081 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
        let uu____3105 =
          let uu____3106 =
            let uu____3107 =
              let uu____3108 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____3108 in
            let uu____3109 =
              let uu____3112 =
                let uu____3113 = embed_term ty in
                FStar_Syntax_Syntax.as_arg uu____3113 in
              let uu____3114 =
                let uu____3117 =
                  let uu____3118 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____3118 in
                [uu____3117] in
              uu____3112 :: uu____3114 in
            uu____3107 :: uu____3109 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Let
            uu____3106 in
        uu____3105 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3126 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3126 with
    | (hd1,args) ->
        let uu____3163 =
          let uu____3176 =
            let uu____3177 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3177.FStar_Syntax_Syntax.n in
          (uu____3176, args) in
        (match uu____3163 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3190)::(bs,uu____3192)::(t2,uu____3194)::(dcs,uu____3196)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3251 =
               let uu____3264 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____3267 = unembed_binders bs in
               let uu____3270 = unembed_term t2 in
               let uu____3271 =
                 FStar_Syntax_Embeddings.unembed_list unembed_ctor dcs in
               (uu____3264, uu____3267, uu____3270, uu____3271) in
             FStar_Reflection_Data.Sg_Inductive uu____3251
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____3282)::(ty,uu____3284)::(t2,uu____3286)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let_lid
             ->
             let uu____3331 =
               let uu____3338 = unembed_fvar fvar1 in
               let uu____3339 = unembed_term ty in
               let uu____3340 = unembed_term t2 in
               (uu____3338, uu____3339, uu____3340) in
             FStar_Reflection_Data.Sg_Let uu____3331
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____3356 -> failwith "not an embedded sigelt_view")
let binders_of_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders
  = fun e  -> FStar_TypeChecker_Env.all_binders e
let type_of_binder:
  'Auu____3377 .
    (FStar_Syntax_Syntax.bv,'Auu____3377) FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun b  -> match b with | (b1,uu____3393) -> b1.FStar_Syntax_Syntax.sort
let term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  FStar_Syntax_Util.term_eq
let fresh_binder:
  'Auu____3404 .
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.bv,'Auu____3404 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____3415 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t in
    (uu____3415, FStar_Pervasives_Native.None)
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  FStar_Syntax_Print.term_to_string