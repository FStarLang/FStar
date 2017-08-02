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
  fun t  -> protect_embedded_term FStar_Reflection_Data.fstar_refl_term t
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
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____684 =
          let uu____685 =
            let uu____686 =
              let uu____687 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____687 in
            [uu____686] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____685 in
        uu____684 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____691 =
          let uu____692 =
            let uu____693 =
              let uu____694 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____694 in
            [uu____693] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____692 in
        uu____691 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____699 =
          let uu____700 =
            let uu____701 =
              let uu____702 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____702 in
            let uu____703 =
              let uu____706 =
                let uu____707 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____707 in
              [uu____706] in
            uu____701 :: uu____703 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____700 in
        uu____699 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____712 =
          let uu____713 =
            let uu____714 =
              let uu____715 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____715 in
            let uu____716 =
              let uu____719 =
                let uu____720 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____720 in
              [uu____719] in
            uu____714 :: uu____716 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____713 in
        uu____712 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____725 =
          let uu____726 =
            let uu____727 =
              let uu____728 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____728 in
            let uu____729 =
              let uu____732 =
                let uu____733 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____733 in
              [uu____732] in
            uu____727 :: uu____729 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____726 in
        uu____725 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____737 =
          let uu____738 =
            let uu____739 =
              let uu____740 = FStar_Syntax_Embeddings.embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____740 in
            [uu____739] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____738 in
        uu____737 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____745 =
          let uu____746 =
            let uu____747 =
              let uu____748 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____748 in
            let uu____749 =
              let uu____752 =
                let uu____753 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____753 in
              [uu____752] in
            uu____747 :: uu____749 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____746 in
        uu____745 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____757 =
          let uu____758 =
            let uu____759 =
              let uu____760 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____760 in
            [uu____759] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____758 in
        uu____757 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____765 =
          let uu____766 =
            let uu____767 =
              let uu____768 = FStar_Syntax_Embeddings.embed_int u in
              FStar_Syntax_Syntax.as_arg uu____768 in
            let uu____769 =
              let uu____772 =
                let uu____773 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____773 in
              [uu____772] in
            uu____767 :: uu____769 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____766 in
        uu____765 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____782 =
          let uu____783 =
            let uu____784 =
              let uu____785 = embed_term t1 in
              FStar_Syntax_Syntax.as_arg uu____785 in
            let uu____786 =
              let uu____789 =
                let uu____790 =
                  FStar_Syntax_Embeddings.embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs in
                FStar_Syntax_Syntax.as_arg uu____790 in
              [uu____789] in
            uu____784 :: uu____786 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____783 in
        uu____782 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____802 = FStar_Syntax_Util.head_and_args t1 in
    match uu____802 with
    | (hd1,args) ->
        let uu____839 =
          let uu____852 =
            let uu____853 = FStar_Syntax_Util.un_uinst hd1 in
            uu____853.FStar_Syntax_Syntax.n in
          (uu____852, args) in
        (match uu____839 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____866)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____891 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____891
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____894)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____919 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____919
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____922)::(r,uu____924)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____959 =
               let uu____964 = unembed_term l in
               let uu____965 = unembed_term r in (uu____964, uu____965) in
             FStar_Reflection_Data.Tv_App uu____959
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____968)::(t2,uu____970)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1005 =
               let uu____1010 = unembed_binder b in
               let uu____1011 = unembed_term t2 in (uu____1010, uu____1011) in
             FStar_Reflection_Data.Tv_Abs uu____1005
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1014)::(t2,uu____1016)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1051 =
               let uu____1056 = unembed_binder b in
               let uu____1057 = unembed_term t2 in (uu____1056, uu____1057) in
             FStar_Reflection_Data.Tv_Arrow uu____1051
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1060)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             (FStar_Syntax_Embeddings.unembed_unit u;
              FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1088)::(t2,uu____1090)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1125 =
               let uu____1130 = unembed_binder b in
               let uu____1131 = unembed_term t2 in (uu____1130, uu____1131) in
             FStar_Reflection_Data.Tv_Refine uu____1125
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1134)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1159 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1159
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1162)::(t2,uu____1164)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1199 =
               let uu____1204 = FStar_Syntax_Embeddings.unembed_int u in
               let uu____1205 = unembed_term t2 in (uu____1204, uu____1205) in
             FStar_Reflection_Data.Tv_Uvar uu____1199
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1208)::(brs,uu____1210)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1245 =
               let uu____1252 = unembed_term t2 in
               let uu____1253 =
                 FStar_Syntax_Embeddings.unembed_list unembed_branch brs in
               (uu____1252, uu____1253) in
             FStar_Reflection_Data.Tv_Match uu____1245
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1285 -> failwith "not an embedded term_view")
let rec last: 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____1312::xs -> last xs
let rec init: 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____1338 = init xs in x :: uu____1338
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1349 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1349
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1358 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1358
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____1368) ->
        let uu____1381 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____1381
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (bs,uu____1383) ->
        FStar_Reflection_Data.C_String (FStar_Util.string_of_bytes bs)
    | uu____1388 ->
        let uu____1389 =
          let uu____1390 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____1390 in
        failwith uu____1389
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1397 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1397
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1440 = last args in
        (match uu____1440 with
         | (a,uu____1454) ->
             let uu____1459 =
               let uu____1464 =
                 let uu____1467 =
                   let uu____1468 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1468 in
                 uu____1467 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos in
               (uu____1464, a) in
             FStar_Reflection_Data.Tv_App uu____1459)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1481,uu____1482) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1524 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1524 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1551 =
                    let uu____1556 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1556) in
                  FStar_Reflection_Data.Tv_Abs uu____1551))
    | FStar_Syntax_Syntax.Tm_type uu____1561 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1595 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1595 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1622 =
                    let uu____1627 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1627) in
                  FStar_Reflection_Data.Tv_Arrow uu____1622))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1643 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1643 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1672 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1682 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____1682
    | FStar_Syntax_Syntax.Tm_uvar (u,t2) ->
        let uu____1709 =
          let uu____1714 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____1714, t2) in
        FStar_Reflection_Data.Tv_Uvar uu____1709
    | FStar_Syntax_Syntax.Tm_match (t2,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____1764 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____1764
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____1783 =
                let uu____1790 =
                  FStar_List.map
                    (fun uu____1802  ->
                       match uu____1802 with
                       | (p1,uu____1810) -> inspect_pat p1) ps in
                (fv, uu____1790) in
              FStar_Reflection_Data.Pat_Cons uu____1783
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____1819 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___80_1863  ->
               match uu___80_1863 with
               | (pat,uu____1885,t3) ->
                   let uu____1903 = inspect_pat pat in (uu____1903, t3)) brs1 in
        FStar_Reflection_Data.Tv_Match (t2, brs2)
    | uu____1916 ->
        ((let uu____1918 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1919 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1918 uu____1919);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____1925 =
          let uu____1936 = FStar_Util.string_of_int i in
          (uu____1936, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____1925
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string
          ((FStar_Util.bytes_of_string s), FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1955) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1959 =
          let uu____1968 = FStar_Syntax_Syntax.as_arg r in [uu____1968] in
        FStar_Syntax_Util.mk_app l uu____1959
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1973 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1973
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1977),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____1984 =
          let uu____1987 =
            let uu____1988 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____1988 in
          FStar_Syntax_Syntax.mk uu____1987 in
        uu____1984 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
              let uu____2011 =
                let uu____2012 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____2012 in
              FStar_All.pipe_left wrap uu____2011
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2021 =
                let uu____2022 =
                  let uu____2035 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2049 = pack_pat p1 in (uu____2049, false))
                      ps in
                  (fv, uu____2035) in
                FStar_Syntax_Syntax.Pat_cons uu____2022 in
              FStar_All.pipe_left wrap uu____2021
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___81_2095  ->
               match uu___81_2095 with
               | (pat,t1) ->
                   let uu____2112 = pack_pat pat in
                   (uu____2112, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | uu____2124 -> failwith "pack: unexpected term view"
let embed_order: FStar_Order.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Order.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2134 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2134 with
    | (hd1,args) ->
        let uu____2171 =
          let uu____2184 =
            let uu____2185 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2185.FStar_Syntax_Syntax.n in
          (uu____2184, args) in
        (match uu____2171 with
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
         | uu____2241 -> failwith "not an embedded order")
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
    let uu____2282 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2282 with
    | (hd1,args) ->
        let uu____2319 =
          let uu____2332 =
            let uu____2333 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2333.FStar_Syntax_Syntax.n in
          (uu____2332, args) in
        (match uu____2319 with
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
         | uu____2404 -> failwith "not an embedded norm_step")
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____2469,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____2570,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____2587 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____2587 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____2660,n1,uu____2662) ->
                          let uu____2667 =
                            let uu____2672 = FStar_Ident.path_of_lid lid2 in
                            (uu____2672, t1) in
                          FStar_Reflection_Data.Ctor uu____2667
                      | uu____2677 -> failwith "wat 1")
                 | uu____2678 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | uu____2706 -> FStar_Reflection_Data.Unk)
let embed_ctor: FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____2713 =
          let uu____2714 =
            let uu____2715 =
              let uu____2716 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2716 in
            let uu____2717 =
              let uu____2720 =
                let uu____2721 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____2721 in
              [uu____2720] in
            uu____2715 :: uu____2717 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____2714 in
        uu____2713 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2729 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2729 with
    | (hd1,args) ->
        let uu____2766 =
          let uu____2779 =
            let uu____2780 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2780.FStar_Syntax_Syntax.n in
          (uu____2779, args) in
        (match uu____2766 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2793)::(t2,uu____2795)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____2830 =
               let uu____2835 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____2838 = unembed_term t2 in (uu____2835, uu____2838) in
             FStar_Reflection_Data.Ctor uu____2830
         | uu____2841 -> failwith "not an embedded ctor")
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____2870 =
          let uu____2871 =
            let uu____2872 =
              let uu____2873 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2873 in
            let uu____2874 =
              let uu____2877 =
                let uu____2878 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____2878 in
              let uu____2879 =
                let uu____2882 =
                  let uu____2883 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____2883 in
                let uu____2884 =
                  let uu____2887 =
                    let uu____2888 =
                      FStar_Syntax_Embeddings.embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____2888 in
                  [uu____2887] in
                uu____2882 :: uu____2884 in
              uu____2877 :: uu____2879 in
            uu____2872 :: uu____2874 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____2871 in
        uu____2870 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2896 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2896 with
    | (hd1,args) ->
        let uu____2933 =
          let uu____2946 =
            let uu____2947 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2947.FStar_Syntax_Syntax.n in
          (uu____2946, args) in
        (match uu____2933 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2960)::(bs,uu____2962)::(t2,uu____2964)::(dcs,uu____2966)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3021 =
               let uu____3034 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____3037 = unembed_binders bs in
               let uu____3040 = unembed_term t2 in
               let uu____3041 =
                 FStar_Syntax_Embeddings.unembed_list unembed_ctor dcs in
               (uu____3034, uu____3037, uu____3040, uu____3041) in
             FStar_Reflection_Data.Sg_Inductive uu____3021
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____3065 -> failwith "not an embedded sigelt_view")
let binders_of_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders
  = fun e  -> FStar_TypeChecker_Env.all_binders e
let type_of_binder:
  'Auu____3086 .
    (FStar_Syntax_Syntax.bv,'Auu____3086) FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun b  -> match b with | (b1,uu____3102) -> b1.FStar_Syntax_Syntax.sort
let term_eq:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool
  = FStar_Syntax_Util.term_eq
let fresh_binder:
  'Auu____3117 .
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.bv,'Auu____3117 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____3128 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t in
    (uu____3128, FStar_Pervasives_Native.None)
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  FStar_Syntax_Print.term_to_string