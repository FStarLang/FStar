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
let embed_comp: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term =
  fun c  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_comp c
      "reflection.embed_comp" FStar_Pervasives_Native.None
let unembed_comp: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp =
  fun t  ->
    let uu____195 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____195 FStar_Dyn.undyn
let embed_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term =
  fun env  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_env env
      "tactics_embed_env" FStar_Pervasives_Native.None
let unembed_env: FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env =
  fun t  ->
    let uu____204 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____204 FStar_Dyn.undyn
let embed_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
    | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
    | FStar_Reflection_Data.C_Int i ->
        let uu____210 =
          let uu____211 =
            let uu____212 =
              let uu____213 =
                let uu____214 = FStar_Util.string_of_int i in
                FStar_Syntax_Util.exp_int uu____214 in
              FStar_Syntax_Syntax.as_arg uu____213 in
            [uu____212] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____211 in
        uu____210 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_String s ->
        let uu____218 =
          let uu____219 =
            let uu____220 =
              let uu____221 = FStar_Syntax_Embeddings.embed_string s in
              FStar_Syntax_Syntax.as_arg uu____221 in
            [uu____220] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String
            uu____219 in
        uu____218 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____229 = FStar_Syntax_Util.head_and_args t1 in
    match uu____229 with
    | (hd1,args) ->
        let uu____266 =
          let uu____279 =
            let uu____280 = FStar_Syntax_Util.un_uinst hd1 in
            uu____280.FStar_Syntax_Syntax.n in
          (uu____279, args) in
        (match uu____266 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____338)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____363 = FStar_Syntax_Embeddings.unembed_int i in
             FStar_Reflection_Data.C_Int uu____363
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____366)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____391 = FStar_Syntax_Embeddings.unembed_string s in
             FStar_Reflection_Data.C_String uu____391
         | uu____392 -> failwith "not an embedded vconst")
let rec embed_pattern:
  FStar_Reflection_Data.pattern -> FStar_Syntax_Syntax.term =
  fun p  ->
    match p with
    | FStar_Reflection_Data.Pat_Constant c ->
        let uu____410 =
          let uu____411 =
            let uu____412 =
              let uu____413 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____413 in
            [uu____412] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant uu____411 in
        uu____410 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
        let uu____422 =
          let uu____423 =
            let uu____424 =
              let uu____425 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____425 in
            let uu____426 =
              let uu____429 =
                let uu____430 =
                  FStar_Syntax_Embeddings.embed_list embed_pattern
                    FStar_Reflection_Data.fstar_refl_pattern ps in
                FStar_Syntax_Syntax.as_arg uu____430 in
              [uu____429] in
            uu____424 :: uu____426 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
            uu____423 in
        uu____422 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Var bv ->
        let uu____434 =
          let uu____435 =
            let uu____436 =
              let uu____437 =
                let uu____438 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____438 in
              FStar_Syntax_Syntax.as_arg uu____437 in
            [uu____436] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
            uu____435 in
        uu____434 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Wild bv ->
        let uu____442 =
          let uu____443 =
            let uu____444 =
              let uu____445 =
                let uu____446 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____446 in
              FStar_Syntax_Syntax.as_arg uu____445 in
            [uu____444] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____443 in
        uu____442 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_pattern:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.pattern =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____454 = FStar_Syntax_Util.head_and_args t1 in
    match uu____454 with
    | (hd1,args) ->
        let uu____491 =
          let uu____504 =
            let uu____505 = FStar_Syntax_Util.un_uinst hd1 in
            uu____505.FStar_Syntax_Syntax.n in
          (uu____504, args) in
        (match uu____491 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____518)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____543 = unembed_const c in
             FStar_Reflection_Data.Pat_Constant uu____543
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____546)::(ps,uu____548)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____583 =
               let uu____590 = unembed_fvar f in
               let uu____591 =
                 FStar_Syntax_Embeddings.unembed_list unembed_pattern ps in
               (uu____590, uu____591) in
             FStar_Reflection_Data.Pat_Cons uu____583
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____598)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____623 =
               let uu____624 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____624 in
             FStar_Reflection_Data.Pat_Var uu____623
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____631)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____656 =
               let uu____657 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____657 in
             FStar_Reflection_Data.Pat_Wild uu____656
         | uu____662 -> failwith "not an embedded pattern")
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
    let uu____698 = FStar_Syntax_Util.head_and_args t1 in
    match uu____698 with
    | (hd1,args) ->
        let uu____735 =
          let uu____748 =
            let uu____749 = FStar_Syntax_Util.un_uinst hd1 in
            uu____749.FStar_Syntax_Syntax.n in
          (uu____748, args) in
        (match uu____735 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit_lid
             -> FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit_lid
             -> FStar_Reflection_Data.Q_Implicit
         | uu____790 -> failwith "not an embedded aqualv")
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
        let uu____822 =
          let uu____823 =
            let uu____824 =
              let uu____825 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____825 in
            [uu____824] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____823 in
        uu____822 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____829 =
          let uu____830 =
            let uu____831 =
              let uu____832 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____832 in
            [uu____831] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____830 in
        uu____829 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____837 =
          let uu____838 =
            let uu____839 =
              let uu____840 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____840 in
            let uu____841 =
              let uu____844 =
                let uu____845 = embed_argv a in
                FStar_Syntax_Syntax.as_arg uu____845 in
              [uu____844] in
            uu____839 :: uu____841 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____838 in
        uu____837 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____850 =
          let uu____851 =
            let uu____852 =
              let uu____853 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____853 in
            let uu____854 =
              let uu____857 =
                let uu____858 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____858 in
              [uu____857] in
            uu____852 :: uu____854 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____851 in
        uu____850 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____863 =
          let uu____864 =
            let uu____865 =
              let uu____866 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____866 in
            let uu____867 =
              let uu____870 =
                let uu____871 = embed_comp c in
                FStar_Syntax_Syntax.as_arg uu____871 in
              [uu____870] in
            uu____865 :: uu____867 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____864 in
        uu____863 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____875 =
          let uu____876 =
            let uu____877 =
              let uu____878 = FStar_Syntax_Embeddings.embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____878 in
            [uu____877] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____876 in
        uu____875 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____883 =
          let uu____884 =
            let uu____885 =
              let uu____886 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____886 in
            let uu____887 =
              let uu____890 =
                let uu____891 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____891 in
              [uu____890] in
            uu____885 :: uu____887 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____884 in
        uu____883 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____895 =
          let uu____896 =
            let uu____897 =
              let uu____898 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____898 in
            [uu____897] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____896 in
        uu____895 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____903 =
          let uu____904 =
            let uu____905 =
              let uu____906 = FStar_Syntax_Embeddings.embed_int u in
              FStar_Syntax_Syntax.as_arg uu____906 in
            let uu____907 =
              let uu____910 =
                let uu____911 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____911 in
              [uu____910] in
            uu____905 :: uu____907 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____904 in
        uu____903 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let uu____917 =
          let uu____918 =
            let uu____919 =
              let uu____920 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____920 in
            let uu____921 =
              let uu____924 =
                let uu____925 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____925 in
              let uu____926 =
                let uu____929 =
                  let uu____930 = embed_term t2 in
                  FStar_Syntax_Syntax.as_arg uu____930 in
                [uu____929] in
              uu____924 :: uu____926 in
            uu____919 :: uu____921 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let
            uu____918 in
        uu____917 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____939 =
          let uu____940 =
            let uu____941 =
              let uu____942 = embed_term t1 in
              FStar_Syntax_Syntax.as_arg uu____942 in
            let uu____943 =
              let uu____946 =
                let uu____947 =
                  FStar_Syntax_Embeddings.embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs in
                FStar_Syntax_Syntax.as_arg uu____947 in
              [uu____946] in
            uu____941 :: uu____943 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____940 in
        uu____939 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____959 = FStar_Syntax_Util.head_and_args t1 in
    match uu____959 with
    | (hd1,args) ->
        let uu____996 =
          let uu____1009 =
            let uu____1010 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1010.FStar_Syntax_Syntax.n in
          (uu____1009, args) in
        (match uu____996 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1023)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1048 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1048
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1051)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1076 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1076
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1079)::(r,uu____1081)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1116 =
               let uu____1121 = unembed_term l in
               let uu____1122 = unembed_argv r in (uu____1121, uu____1122) in
             FStar_Reflection_Data.Tv_App uu____1116
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1133)::(t2,uu____1135)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1170 =
               let uu____1175 = unembed_binder b in
               let uu____1176 = unembed_term t2 in (uu____1175, uu____1176) in
             FStar_Reflection_Data.Tv_Abs uu____1170
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1179)::(t2,uu____1181)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1216 =
               let uu____1221 = unembed_binder b in
               let uu____1222 = unembed_comp t2 in (uu____1221, uu____1222) in
             FStar_Reflection_Data.Tv_Arrow uu____1216
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1225)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             (FStar_Syntax_Embeddings.unembed_unit u;
              FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1253)::(t2,uu____1255)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1290 =
               let uu____1295 = unembed_binder b in
               let uu____1296 = unembed_term t2 in (uu____1295, uu____1296) in
             FStar_Reflection_Data.Tv_Refine uu____1290
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1299)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1324 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1324
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1327)::(t2,uu____1329)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1364 =
               let uu____1369 = FStar_Syntax_Embeddings.unembed_int u in
               let uu____1370 = unembed_term t2 in (uu____1369, uu____1370) in
             FStar_Reflection_Data.Tv_Uvar uu____1364
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1373)::(t11,uu____1375)::(t2,uu____1377)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let_lid
             ->
             let uu____1422 =
               let uu____1429 = unembed_binder b in
               let uu____1430 = unembed_term t11 in
               let uu____1431 = unembed_term t2 in
               (uu____1429, uu____1430, uu____1431) in
             FStar_Reflection_Data.Tv_Let uu____1422
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1434)::(brs,uu____1436)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1471 =
               let uu____1478 = unembed_term t2 in
               let uu____1479 =
                 FStar_Syntax_Embeddings.unembed_list unembed_branch brs in
               (uu____1478, uu____1479) in
             FStar_Reflection_Data.Tv_Match uu____1471
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1511 -> failwith "not an embedded term_view")
let embed_comp_view:
  FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t ->
        let uu____1529 =
          let uu____1530 =
            let uu____1531 =
              let uu____1532 = embed_term t in
              FStar_Syntax_Syntax.as_arg uu____1532 in
            [uu____1531] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Total
            uu____1530 in
        uu____1529 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let uu____1537 =
          let uu____1538 =
            let uu____1539 =
              let uu____1540 = embed_term pre in
              FStar_Syntax_Syntax.as_arg uu____1540 in
            let uu____1541 =
              let uu____1544 =
                let uu____1545 = embed_term post in
                FStar_Syntax_Syntax.as_arg uu____1545 in
              [uu____1544] in
            uu____1539 :: uu____1541 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Lemma
            uu____1538 in
        uu____1537 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_Unknown  -> FStar_Reflection_Data.ref_C_Unknown
let unembed_comp_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.comp_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1553 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1553 with
    | (hd1,args) ->
        let uu____1590 =
          let uu____1603 =
            let uu____1604 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1604.FStar_Syntax_Syntax.n in
          (uu____1603, args) in
        (match uu____1590 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____1617)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total_lid
             ->
             let uu____1642 = unembed_term t2 in
             FStar_Reflection_Data.C_Total uu____1642
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____1645)::(post,uu____1647)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma_lid
             ->
             let uu____1682 =
               let uu____1687 = unembed_term pre in
               let uu____1688 = unembed_term post in (uu____1687, uu____1688) in
             FStar_Reflection_Data.C_Lemma uu____1682
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown_lid
             -> FStar_Reflection_Data.C_Unknown
         | uu____1704 -> failwith "not an embedded comp_view")
let rec last: 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____1731::xs -> last xs
let rec init: 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____1757 = init xs in x :: uu____1757
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1768 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1768
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1777 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1777
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____1787) ->
        let uu____1800 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____1800
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____1802) ->
        FStar_Reflection_Data.C_String s
    | uu____1803 ->
        let uu____1804 =
          let uu____1805 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____1805 in
        failwith uu____1804
let rec inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let t2 = FStar_Syntax_Util.un_uinst t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____1813) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1819 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1819
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1862 = last args in
        (match uu____1862 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____1882) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit in
             let uu____1883 =
               let uu____1888 =
                 let uu____1891 =
                   let uu____1892 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1892 in
                 uu____1891 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos in
               (uu____1888, (a, q')) in
             FStar_Reflection_Data.Tv_App uu____1883)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1911,uu____1912) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____1954 = FStar_Syntax_Subst.open_term bs t3 in
        (match uu____1954 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1981 =
                    let uu____1986 = FStar_Syntax_Util.abs bs2 t4 k in
                    (b, uu____1986) in
                  FStar_Reflection_Data.Tv_Abs uu____1981))
    | FStar_Syntax_Syntax.Tm_type uu____1991 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____2007 ->
        let uu____2020 = FStar_Syntax_Util.arrow_one t2 in
        (match uu____2020 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____2044 = FStar_Syntax_Subst.open_term [b] t3 in
        (match uu____2044 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2073 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2083 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____2083
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2110 =
          let uu____2115 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____2115, t3) in
        FStar_Reflection_Data.Tv_Uvar uu____2110
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2135 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____2138 = FStar_Syntax_Subst.open_term [b] t21 in
               (match uu____2138 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2167 ->
                          failwith
                            "impossible: open_term returned different amount of binders" in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2225 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____2225
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2244 =
                let uu____2251 =
                  FStar_List.map
                    (fun uu____2263  ->
                       match uu____2263 with
                       | (p1,uu____2271) -> inspect_pat p1) ps in
                (fv, uu____2251) in
              FStar_Reflection_Data.Pat_Cons uu____2244
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2280 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___103_2324  ->
               match uu___103_2324 with
               | (pat,uu____2346,t4) ->
                   let uu____2364 = inspect_pat pat in (uu____2364, t4)) brs1 in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2377 ->
        ((let uu____2379 = FStar_Syntax_Print.tag_of_term t2 in
          let uu____2380 = FStar_Syntax_Print.term_to_string t2 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____2379 uu____2380);
         FStar_Reflection_Data.Tv_Unknown)
let inspect_comp: FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2386) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2397)::(post,uu____2399)::uu____2400 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2433 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2443 ->
        FStar_Reflection_Data.C_Unknown
let pack_comp: FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2457 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2463 =
          let uu____2474 = FStar_Util.string_of_int i in
          (uu____2474, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____2463
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2491) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2500 =
               let uu____2509 = FStar_Syntax_Syntax.as_arg r in [uu____2509] in
             FStar_Syntax_Util.mk_app l uu____2500
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2510 =
               let uu____2519 = FStar_Syntax_Syntax.iarg r in [uu____2519] in
             FStar_Syntax_Util.mk_app l uu____2510)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2525),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2532 =
          let uu____2535 =
            let uu____2536 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____2536 in
          FStar_Syntax_Syntax.mk uu____2535 in
        uu____2532 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        FStar_Syntax_Util.uvar_from_id u t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 in
        let uu____2547 =
          let uu____2550 =
            let uu____2551 =
              let uu____2564 = FStar_Syntax_Subst.close [b] t2 in
              ((false, [lb]), uu____2564) in
            FStar_Syntax_Syntax.Tm_let uu____2551 in
          FStar_Syntax_Syntax.mk uu____2550 in
        uu____2547 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2593 =
                let uu____2594 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____2594 in
              FStar_All.pipe_left wrap uu____2593
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2603 =
                let uu____2604 =
                  let uu____2617 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2631 = pack_pat p1 in (uu____2631, false))
                      ps in
                  (fv, uu____2617) in
                FStar_Syntax_Syntax.Pat_cons uu____2604 in
              FStar_All.pipe_left wrap uu____2603
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___104_2677  ->
               match uu___104_2677 with
               | (pat,t1) ->
                   let uu____2694 = pack_pat pat in
                   (uu____2694, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        failwith "pack: unexpected term view"
let embed_order: FStar_Order.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Order.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2715 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2715 with
    | (hd1,args) ->
        let uu____2752 =
          let uu____2765 =
            let uu____2766 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2766.FStar_Syntax_Syntax.n in
          (uu____2765, args) in
        (match uu____2752 with
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
         | uu____2822 -> failwith "not an embedded order")
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____2906,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____3007,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____3024 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____3024 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3097,n1,uu____3099) ->
                          let uu____3104 =
                            let uu____3109 = FStar_Ident.path_of_lid lid2 in
                            (uu____3109, t1) in
                          FStar_Reflection_Data.Ctor uu____3104
                      | uu____3114 -> failwith "wat 1")
                 | uu____3115 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3144) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____3159 ->
                     failwith "global Sig_let has bv" in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____3164 -> FStar_Reflection_Data.Unk)
let embed_ctor: FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____3171 =
          let uu____3172 =
            let uu____3173 =
              let uu____3174 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____3174 in
            let uu____3175 =
              let uu____3178 =
                let uu____3179 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____3179 in
              [uu____3178] in
            uu____3173 :: uu____3175 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____3172 in
        uu____3171 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3187 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3187 with
    | (hd1,args) ->
        let uu____3224 =
          let uu____3237 =
            let uu____3238 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3238.FStar_Syntax_Syntax.n in
          (uu____3237, args) in
        (match uu____3224 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3251)::(t2,uu____3253)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3288 =
               let uu____3293 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____3296 = unembed_term t2 in (uu____3293, uu____3296) in
             FStar_Reflection_Data.Ctor uu____3288
         | uu____3299 -> failwith "not an embedded ctor")
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3328 =
          let uu____3329 =
            let uu____3330 =
              let uu____3331 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____3331 in
            let uu____3332 =
              let uu____3335 =
                let uu____3336 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____3336 in
              let uu____3337 =
                let uu____3340 =
                  let uu____3341 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____3341 in
                let uu____3342 =
                  let uu____3345 =
                    let uu____3346 =
                      FStar_Syntax_Embeddings.embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____3346 in
                  [uu____3345] in
                uu____3340 :: uu____3342 in
              uu____3335 :: uu____3337 in
            uu____3330 :: uu____3332 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____3329 in
        uu____3328 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
        let uu____3352 =
          let uu____3353 =
            let uu____3354 =
              let uu____3355 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____3355 in
            let uu____3356 =
              let uu____3359 =
                let uu____3360 = embed_term ty in
                FStar_Syntax_Syntax.as_arg uu____3360 in
              let uu____3361 =
                let uu____3364 =
                  let uu____3365 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____3365 in
                [uu____3364] in
              uu____3359 :: uu____3361 in
            uu____3354 :: uu____3356 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Let
            uu____3353 in
        uu____3352 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3373 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3373 with
    | (hd1,args) ->
        let uu____3410 =
          let uu____3423 =
            let uu____3424 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3424.FStar_Syntax_Syntax.n in
          (uu____3423, args) in
        (match uu____3410 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3437)::(bs,uu____3439)::(t2,uu____3441)::(dcs,uu____3443)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3498 =
               let uu____3511 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____3514 = unembed_binders bs in
               let uu____3517 = unembed_term t2 in
               let uu____3518 =
                 FStar_Syntax_Embeddings.unembed_list unembed_ctor dcs in
               (uu____3511, uu____3514, uu____3517, uu____3518) in
             FStar_Reflection_Data.Sg_Inductive uu____3498
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____3529)::(ty,uu____3531)::(t2,uu____3533)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let_lid
             ->
             let uu____3578 =
               let uu____3585 = unembed_fvar fvar1 in
               let uu____3586 = unembed_term ty in
               let uu____3587 = unembed_term t2 in
               (uu____3585, uu____3586, uu____3587) in
             FStar_Reflection_Data.Sg_Let uu____3578
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____3603 -> failwith "not an embedded sigelt_view")
let binders_of_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders
  = fun e  -> FStar_TypeChecker_Env.all_binders e
let type_of_binder:
  'Auu____3624 .
    (FStar_Syntax_Syntax.bv,'Auu____3624) FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun b  -> match b with | (b1,uu____3640) -> b1.FStar_Syntax_Syntax.sort
let term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  FStar_Syntax_Util.term_eq
let fresh_binder:
  'Auu____3651 .
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.bv,'Auu____3651 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____3662 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t in
    (uu____3662, FStar_Pervasives_Native.None)
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  FStar_Syntax_Print.term_to_string