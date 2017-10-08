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
    let uu____29 =
      let uu____44 = FStar_Syntax_Util.unmeta t in
      FStar_Syntax_Util.head_and_args uu____44 in
    match uu____29 with
    | (head1,args) ->
        let uu____67 =
          let uu____80 =
            let uu____81 = FStar_Syntax_Util.un_uinst head1 in
            uu____81.FStar_Syntax_Syntax.n in
          (uu____80, args) in
        (match uu____67 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____93::(x,uu____95)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_refl_embed_lid
             -> x
         | uu____132 ->
             let uu____145 =
               let uu____146 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____146 in
             failwith uu____145)
let embed_binder: FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term =
  fun b  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_binder b
      "reflection.embed_binder" FStar_Pervasives_Native.None
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let uu____155 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____155 FStar_Dyn.undyn
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
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_fvar fv
      "reflection.embed_fvar" FStar_Pervasives_Native.None
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____186 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____186 FStar_Dyn.undyn
let embed_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term =
  fun env  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_env env
      "tactics_embed_env" FStar_Pervasives_Native.None
let unembed_env: FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env =
  fun t  ->
    let uu____195 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____195 FStar_Dyn.undyn
let embed_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
    | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
    | FStar_Reflection_Data.C_Int i ->
        let uu____201 =
          let uu____202 =
            let uu____203 =
              let uu____204 =
                let uu____205 = FStar_Util.string_of_int i in
                FStar_Syntax_Util.exp_int uu____205 in
              FStar_Syntax_Syntax.as_arg uu____204 in
            [uu____203] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____202 in
        uu____201 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_String s ->
        let uu____209 =
          let uu____210 =
            let uu____211 =
              let uu____212 = FStar_Syntax_Embeddings.embed_string s in
              FStar_Syntax_Syntax.as_arg uu____212 in
            [uu____211] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String
            uu____210 in
        uu____209 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____220 = FStar_Syntax_Util.head_and_args t1 in
    match uu____220 with
    | (hd1,args) ->
        let uu____257 =
          let uu____270 =
            let uu____271 = FStar_Syntax_Util.un_uinst hd1 in
            uu____271.FStar_Syntax_Syntax.n in
          (uu____270, args) in
        (match uu____257 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____329)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____354 = FStar_Syntax_Embeddings.unembed_int i in
             FStar_Reflection_Data.C_Int uu____354
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____357)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____382 = FStar_Syntax_Embeddings.unembed_string s in
             FStar_Reflection_Data.C_String uu____382
         | uu____383 -> failwith "not an embedded vconst")
let rec embed_pattern:
  FStar_Reflection_Data.pattern -> FStar_Syntax_Syntax.term =
  fun p  ->
    match p with
    | FStar_Reflection_Data.Pat_Constant c ->
        let uu____401 =
          let uu____402 =
            let uu____403 =
              let uu____404 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____404 in
            [uu____403] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant uu____402 in
        uu____401 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
        let uu____413 =
          let uu____414 =
            let uu____415 =
              let uu____416 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____416 in
            let uu____417 =
              let uu____420 =
                let uu____421 =
                  FStar_Syntax_Embeddings.embed_list embed_pattern
                    FStar_Reflection_Data.fstar_refl_pattern ps in
                FStar_Syntax_Syntax.as_arg uu____421 in
              [uu____420] in
            uu____415 :: uu____417 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
            uu____414 in
        uu____413 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Var bv ->
        let uu____425 =
          let uu____426 =
            let uu____427 =
              let uu____428 =
                let uu____429 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____429 in
              FStar_Syntax_Syntax.as_arg uu____428 in
            [uu____427] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
            uu____426 in
        uu____425 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Wild bv ->
        let uu____433 =
          let uu____434 =
            let uu____435 =
              let uu____436 =
                let uu____437 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____437 in
              FStar_Syntax_Syntax.as_arg uu____436 in
            [uu____435] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____434 in
        uu____433 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_pattern:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.pattern =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____445 = FStar_Syntax_Util.head_and_args t1 in
    match uu____445 with
    | (hd1,args) ->
        let uu____482 =
          let uu____495 =
            let uu____496 = FStar_Syntax_Util.un_uinst hd1 in
            uu____496.FStar_Syntax_Syntax.n in
          (uu____495, args) in
        (match uu____482 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____509)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____534 = unembed_const c in
             FStar_Reflection_Data.Pat_Constant uu____534
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____537)::(ps,uu____539)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____574 =
               let uu____581 = unembed_fvar f in
               let uu____582 =
                 FStar_Syntax_Embeddings.unembed_list unembed_pattern ps in
               (uu____581, uu____582) in
             FStar_Reflection_Data.Pat_Cons uu____574
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____589)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____614 =
               let uu____615 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____615 in
             FStar_Reflection_Data.Pat_Var uu____614
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____622)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____647 =
               let uu____648 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____648 in
             FStar_Reflection_Data.Pat_Wild uu____647
         | uu____653 -> failwith "not an embedded pattern")
let embed_branch:
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  FStar_Syntax_Embeddings.embed_pair embed_pattern
    FStar_Reflection_Data.fstar_refl_pattern embed_term
    FStar_Syntax_Syntax.t_term
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
    let uu____689 = FStar_Syntax_Util.head_and_args t1 in
    match uu____689 with
    | (hd1,args) ->
        let uu____726 =
          let uu____739 =
            let uu____740 = FStar_Syntax_Util.un_uinst hd1 in
            uu____740.FStar_Syntax_Syntax.n in
          (uu____739, args) in
        (match uu____726 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit_lid
             -> FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit_lid
             -> FStar_Reflection_Data.Q_Implicit
         | uu____781 -> failwith "not an embedded aqualv")
let embed_argv:
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  FStar_Syntax_Embeddings.embed_pair embed_term FStar_Syntax_Syntax.t_term
    embed_aqualv FStar_Reflection_Data.fstar_refl_aqualv
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
        let uu____813 =
          let uu____814 =
            let uu____815 =
              let uu____816 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____816 in
            [uu____815] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____814 in
        uu____813 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____820 =
          let uu____821 =
            let uu____822 =
              let uu____823 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____823 in
            [uu____822] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____821 in
        uu____820 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____828 =
          let uu____829 =
            let uu____830 =
              let uu____831 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____831 in
            let uu____832 =
              let uu____835 =
                let uu____836 = embed_argv a in
                FStar_Syntax_Syntax.as_arg uu____836 in
              [uu____835] in
            uu____830 :: uu____832 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____829 in
        uu____828 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____841 =
          let uu____842 =
            let uu____843 =
              let uu____844 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____844 in
            let uu____845 =
              let uu____848 =
                let uu____849 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____849 in
              [uu____848] in
            uu____843 :: uu____845 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____842 in
        uu____841 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____854 =
          let uu____855 =
            let uu____856 =
              let uu____857 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____857 in
            let uu____858 =
              let uu____861 =
                let uu____862 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____862 in
              [uu____861] in
            uu____856 :: uu____858 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____855 in
        uu____854 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____866 =
          let uu____867 =
            let uu____868 =
              let uu____869 = FStar_Syntax_Embeddings.embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____869 in
            [uu____868] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____867 in
        uu____866 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____874 =
          let uu____875 =
            let uu____876 =
              let uu____877 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____877 in
            let uu____878 =
              let uu____881 =
                let uu____882 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____882 in
              [uu____881] in
            uu____876 :: uu____878 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____875 in
        uu____874 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____886 =
          let uu____887 =
            let uu____888 =
              let uu____889 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____889 in
            [uu____888] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____887 in
        uu____886 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____894 =
          let uu____895 =
            let uu____896 =
              let uu____897 = FStar_Syntax_Embeddings.embed_int u in
              FStar_Syntax_Syntax.as_arg uu____897 in
            let uu____898 =
              let uu____901 =
                let uu____902 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____902 in
              [uu____901] in
            uu____896 :: uu____898 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____895 in
        uu____894 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let uu____908 =
          let uu____909 =
            let uu____910 =
              let uu____911 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____911 in
            let uu____912 =
              let uu____915 =
                let uu____916 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____916 in
              let uu____917 =
                let uu____920 =
                  let uu____921 = embed_term t2 in
                  FStar_Syntax_Syntax.as_arg uu____921 in
                [uu____920] in
              uu____915 :: uu____917 in
            uu____910 :: uu____912 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let
            uu____909 in
        uu____908 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____930 =
          let uu____931 =
            let uu____932 =
              let uu____933 = embed_term t1 in
              FStar_Syntax_Syntax.as_arg uu____933 in
            let uu____934 =
              let uu____937 =
                let uu____938 =
                  FStar_Syntax_Embeddings.embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs in
                FStar_Syntax_Syntax.as_arg uu____938 in
              [uu____937] in
            uu____932 :: uu____934 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____931 in
        uu____930 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____950 = FStar_Syntax_Util.head_and_args t1 in
    match uu____950 with
    | (hd1,args) ->
        let uu____987 =
          let uu____1000 =
            let uu____1001 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1001.FStar_Syntax_Syntax.n in
          (uu____1000, args) in
        (match uu____987 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1014)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1039 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1039
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1042)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1067 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1067
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1070)::(r,uu____1072)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1107 =
               let uu____1112 = unembed_term l in
               let uu____1113 = unembed_argv r in (uu____1112, uu____1113) in
             FStar_Reflection_Data.Tv_App uu____1107
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1124)::(t2,uu____1126)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1161 =
               let uu____1166 = unembed_binder b in
               let uu____1167 = unembed_term t2 in (uu____1166, uu____1167) in
             FStar_Reflection_Data.Tv_Abs uu____1161
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1170)::(t2,uu____1172)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1207 =
               let uu____1212 = unembed_binder b in
               let uu____1213 = unembed_term t2 in (uu____1212, uu____1213) in
             FStar_Reflection_Data.Tv_Arrow uu____1207
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1216)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             (FStar_Syntax_Embeddings.unembed_unit u;
              FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1244)::(t2,uu____1246)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1281 =
               let uu____1286 = unembed_binder b in
               let uu____1287 = unembed_term t2 in (uu____1286, uu____1287) in
             FStar_Reflection_Data.Tv_Refine uu____1281
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1290)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1315 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1315
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1318)::(t2,uu____1320)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1355 =
               let uu____1360 = FStar_Syntax_Embeddings.unembed_int u in
               let uu____1361 = unembed_term t2 in (uu____1360, uu____1361) in
             FStar_Reflection_Data.Tv_Uvar uu____1355
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1364)::(t11,uu____1366)::(t2,uu____1368)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let_lid
             ->
             let uu____1413 =
               let uu____1420 = unembed_binder b in
               let uu____1421 = unembed_term t11 in
               let uu____1422 = unembed_term t2 in
               (uu____1420, uu____1421, uu____1422) in
             FStar_Reflection_Data.Tv_Let uu____1413
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1425)::(brs,uu____1427)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1462 =
               let uu____1469 = unembed_term t2 in
               let uu____1470 =
                 FStar_Syntax_Embeddings.unembed_list unembed_branch brs in
               (uu____1469, uu____1470) in
             FStar_Reflection_Data.Tv_Match uu____1462
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1502 -> failwith "not an embedded term_view")
let rec last: 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____1529::xs -> last xs
let rec init: 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____1555 = init xs in x :: uu____1555
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1566 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1566
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1575 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1575
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____1585) ->
        let uu____1598 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____1598
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____1600) ->
        FStar_Reflection_Data.C_String s
    | uu____1601 ->
        let uu____1602 =
          let uu____1603 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____1603 in
        failwith uu____1602
let rec inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let t2 = FStar_Syntax_Util.un_uinst t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____1611) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1617 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1617
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1660 = last args in
        (match uu____1660 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____1680) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit in
             let uu____1681 =
               let uu____1686 =
                 let uu____1689 =
                   let uu____1690 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1690 in
                 uu____1689 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos in
               (uu____1686, (a, q')) in
             FStar_Reflection_Data.Tv_App uu____1681)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1709,uu____1710) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____1752 = FStar_Syntax_Subst.open_term bs t3 in
        (match uu____1752 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1779 =
                    let uu____1784 = FStar_Syntax_Util.abs bs2 t4 k in
                    (b, uu____1784) in
                  FStar_Reflection_Data.Tv_Abs uu____1779))
    | FStar_Syntax_Syntax.Tm_type uu____1789 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1823 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1823 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1850 =
                    let uu____1855 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1855) in
                  FStar_Reflection_Data.Tv_Arrow uu____1850))
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1871 = FStar_Syntax_Subst.open_term [b] t3 in
        (match uu____1871 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1900 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1910 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____1910
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____1937 =
          let uu____1942 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____1942, t3) in
        FStar_Reflection_Data.Tv_Uvar uu____1937
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____1962 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____1965 = FStar_Syntax_Subst.open_term [b] t21 in
               (match uu____1965 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____1994 ->
                          failwith
                            "impossible: open_term returned different amount of binders" in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2052 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____2052
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2071 =
                let uu____2078 =
                  FStar_List.map
                    (fun uu____2090  ->
                       match uu____2090 with
                       | (p1,uu____2098) -> inspect_pat p1) ps in
                (fv, uu____2078) in
              FStar_Reflection_Data.Pat_Cons uu____2071
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2107 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___103_2151  ->
               match uu___103_2151 with
               | (pat,uu____2173,t4) ->
                   let uu____2191 = inspect_pat pat in (uu____2191, t4)) brs1 in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2204 ->
        ((let uu____2206 = FStar_Syntax_Print.tag_of_term t2 in
          let uu____2207 = FStar_Syntax_Print.term_to_string t2 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____2206 uu____2207);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2213 =
          let uu____2224 = FStar_Util.string_of_int i in
          (uu____2224, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____2213
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2241) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2250 =
               let uu____2259 = FStar_Syntax_Syntax.as_arg r in [uu____2259] in
             FStar_Syntax_Util.mk_app l uu____2250
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2260 =
               let uu____2269 = FStar_Syntax_Syntax.iarg r in [uu____2269] in
             FStar_Syntax_Util.mk_app l uu____2260)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____2274 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____2274
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2278),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2285 =
          let uu____2288 =
            let uu____2289 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____2289 in
          FStar_Syntax_Syntax.mk uu____2288 in
        uu____2285 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        FStar_Syntax_Util.uvar_from_id u t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 in
        let uu____2300 =
          let uu____2303 =
            let uu____2304 =
              let uu____2317 = FStar_Syntax_Subst.close [b] t2 in
              ((false, [lb]), uu____2317) in
            FStar_Syntax_Syntax.Tm_let uu____2304 in
          FStar_Syntax_Syntax.mk uu____2303 in
        uu____2300 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2346 =
                let uu____2347 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____2347 in
              FStar_All.pipe_left wrap uu____2346
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2356 =
                let uu____2357 =
                  let uu____2370 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2384 = pack_pat p1 in (uu____2384, false))
                      ps in
                  (fv, uu____2370) in
                FStar_Syntax_Syntax.Pat_cons uu____2357 in
              FStar_All.pipe_left wrap uu____2356
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___104_2430  ->
               match uu___104_2430 with
               | (pat,t1) ->
                   let uu____2447 = pack_pat pat in
                   (uu____2447, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | uu____2459 -> failwith "pack: unexpected term view"
let embed_order: FStar_Order.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Order.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2469 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2469 with
    | (hd1,args) ->
        let uu____2506 =
          let uu____2519 =
            let uu____2520 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2520.FStar_Syntax_Syntax.n in
          (uu____2519, args) in
        (match uu____2506 with
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
         | uu____2576 -> failwith "not an embedded order")
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____2660,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____2761,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____2778 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____2778 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____2851,n1,uu____2853) ->
                          let uu____2858 =
                            let uu____2863 = FStar_Ident.path_of_lid lid2 in
                            (uu____2863, t1) in
                          FStar_Reflection_Data.Ctor uu____2858
                      | uu____2868 -> failwith "wat 1")
                 | uu____2869 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2898) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____2913 ->
                     failwith "global Sig_let has bv" in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____2918 -> FStar_Reflection_Data.Unk)
let embed_ctor: FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____2925 =
          let uu____2926 =
            let uu____2927 =
              let uu____2928 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2928 in
            let uu____2929 =
              let uu____2932 =
                let uu____2933 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____2933 in
              [uu____2932] in
            uu____2927 :: uu____2929 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____2926 in
        uu____2925 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2941 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2941 with
    | (hd1,args) ->
        let uu____2978 =
          let uu____2991 =
            let uu____2992 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2992.FStar_Syntax_Syntax.n in
          (uu____2991, args) in
        (match uu____2978 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3005)::(t2,uu____3007)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3042 =
               let uu____3047 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____3050 = unembed_term t2 in (uu____3047, uu____3050) in
             FStar_Reflection_Data.Ctor uu____3042
         | uu____3053 -> failwith "not an embedded ctor")
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3082 =
          let uu____3083 =
            let uu____3084 =
              let uu____3085 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____3085 in
            let uu____3086 =
              let uu____3089 =
                let uu____3090 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____3090 in
              let uu____3091 =
                let uu____3094 =
                  let uu____3095 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____3095 in
                let uu____3096 =
                  let uu____3099 =
                    let uu____3100 =
                      FStar_Syntax_Embeddings.embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____3100 in
                  [uu____3099] in
                uu____3094 :: uu____3096 in
              uu____3089 :: uu____3091 in
            uu____3084 :: uu____3086 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____3083 in
        uu____3082 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
        let uu____3106 =
          let uu____3107 =
            let uu____3108 =
              let uu____3109 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____3109 in
            let uu____3110 =
              let uu____3113 =
                let uu____3114 = embed_term ty in
                FStar_Syntax_Syntax.as_arg uu____3114 in
              let uu____3115 =
                let uu____3118 =
                  let uu____3119 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____3119 in
                [uu____3118] in
              uu____3113 :: uu____3115 in
            uu____3108 :: uu____3110 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Let
            uu____3107 in
        uu____3106 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3127 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3127 with
    | (hd1,args) ->
        let uu____3164 =
          let uu____3177 =
            let uu____3178 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3178.FStar_Syntax_Syntax.n in
          (uu____3177, args) in
        (match uu____3164 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3191)::(bs,uu____3193)::(t2,uu____3195)::(dcs,uu____3197)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3252 =
               let uu____3265 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____3268 = unembed_binders bs in
               let uu____3271 = unembed_term t2 in
               let uu____3272 =
                 FStar_Syntax_Embeddings.unembed_list unembed_ctor dcs in
               (uu____3265, uu____3268, uu____3271, uu____3272) in
             FStar_Reflection_Data.Sg_Inductive uu____3252
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____3283)::(ty,uu____3285)::(t2,uu____3287)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let_lid
             ->
             let uu____3332 =
               let uu____3339 = unembed_fvar fvar1 in
               let uu____3340 = unembed_term ty in
               let uu____3341 = unembed_term t2 in
               (uu____3339, uu____3340, uu____3341) in
             FStar_Reflection_Data.Sg_Let uu____3332
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____3357 -> failwith "not an embedded sigelt_view")
let binders_of_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders
  = fun e  -> FStar_TypeChecker_Env.all_binders e
let type_of_binder:
  'Auu____3378 .
    (FStar_Syntax_Syntax.bv,'Auu____3378) FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun b  -> match b with | (b1,uu____3394) -> b1.FStar_Syntax_Syntax.sort
let term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  FStar_Syntax_Util.term_eq
let fresh_binder:
  'Auu____3405 .
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.bv,'Auu____3405 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____3416 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t in
    (uu____3416, FStar_Pervasives_Native.None)
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  FStar_Syntax_Print.term_to_string