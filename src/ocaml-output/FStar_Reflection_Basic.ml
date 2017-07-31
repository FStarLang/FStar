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
    | FStar_Reflection_Data.Pat_Var (bv,uu____424) ->
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
    | FStar_Reflection_Data.Pat_Wild (bv,uu____433) ->
        let uu____434 =
          let uu____435 =
            let uu____436 =
              let uu____437 =
                let uu____438 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____438 in
              FStar_Syntax_Syntax.as_arg uu____437 in
            [uu____436] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____435 in
        uu____434 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_pattern:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.pattern =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____446 = FStar_Syntax_Util.head_and_args t1 in
    match uu____446 with
    | (hd1,args) ->
        let uu____483 =
          let uu____496 =
            let uu____497 = FStar_Syntax_Util.un_uinst hd1 in
            uu____497.FStar_Syntax_Syntax.n in
          (uu____496, args) in
        (match uu____483 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____510)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____535 = unembed_const c in
             FStar_Reflection_Data.Pat_Constant uu____535
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____538)::(ps,uu____540)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____575 =
               let uu____582 = unembed_fvar f in
               let uu____583 =
                 FStar_Syntax_Embeddings.unembed_list unembed_pattern ps in
               (uu____582, uu____583) in
             FStar_Reflection_Data.Pat_Cons uu____575
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____590)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____615 = unembed_binder b in
             FStar_Reflection_Data.Pat_Var uu____615
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____618)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____643 = unembed_binder b in
             FStar_Reflection_Data.Pat_Wild uu____643
         | uu____644 -> failwith "not an embedded pattern")
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
        let uu____676 =
          let uu____677 =
            let uu____678 =
              let uu____679 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____679 in
            [uu____678] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____677 in
        uu____676 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____683 =
          let uu____684 =
            let uu____685 =
              let uu____686 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____686 in
            [uu____685] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____684 in
        uu____683 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____691 =
          let uu____692 =
            let uu____693 =
              let uu____694 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____694 in
            let uu____695 =
              let uu____698 =
                let uu____699 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____699 in
              [uu____698] in
            uu____693 :: uu____695 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____692 in
        uu____691 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____704 =
          let uu____705 =
            let uu____706 =
              let uu____707 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____707 in
            let uu____708 =
              let uu____711 =
                let uu____712 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____712 in
              [uu____711] in
            uu____706 :: uu____708 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____705 in
        uu____704 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____717 =
          let uu____718 =
            let uu____719 =
              let uu____720 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____720 in
            let uu____721 =
              let uu____724 =
                let uu____725 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____725 in
              [uu____724] in
            uu____719 :: uu____721 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____718 in
        uu____717 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____729 =
          let uu____730 =
            let uu____731 =
              let uu____732 = FStar_Syntax_Embeddings.embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____732 in
            [uu____731] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____730 in
        uu____729 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____737 =
          let uu____738 =
            let uu____739 =
              let uu____740 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____740 in
            let uu____741 =
              let uu____744 =
                let uu____745 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____745 in
              [uu____744] in
            uu____739 :: uu____741 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____738 in
        uu____737 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____749 =
          let uu____750 =
            let uu____751 =
              let uu____752 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____752 in
            [uu____751] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____750 in
        uu____749 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____757 =
          let uu____758 =
            let uu____759 =
              let uu____760 = FStar_Syntax_Embeddings.embed_int u in
              FStar_Syntax_Syntax.as_arg uu____760 in
            let uu____761 =
              let uu____764 =
                let uu____765 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____765 in
              [uu____764] in
            uu____759 :: uu____761 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____758 in
        uu____757 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____774 =
          let uu____775 =
            let uu____776 =
              let uu____777 = embed_term t1 in
              FStar_Syntax_Syntax.as_arg uu____777 in
            let uu____778 =
              let uu____781 =
                let uu____782 =
                  FStar_Syntax_Embeddings.embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs in
                FStar_Syntax_Syntax.as_arg uu____782 in
              [uu____781] in
            uu____776 :: uu____778 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____775 in
        uu____774 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____794 = FStar_Syntax_Util.head_and_args t1 in
    match uu____794 with
    | (hd1,args) ->
        let uu____831 =
          let uu____844 =
            let uu____845 = FStar_Syntax_Util.un_uinst hd1 in
            uu____845.FStar_Syntax_Syntax.n in
          (uu____844, args) in
        (match uu____831 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____858)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____883 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____883
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____886)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____911 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____911
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____914)::(r,uu____916)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____951 =
               let uu____956 = unembed_term l in
               let uu____957 = unembed_term r in (uu____956, uu____957) in
             FStar_Reflection_Data.Tv_App uu____951
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____960)::(t2,uu____962)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____997 =
               let uu____1002 = unembed_binder b in
               let uu____1003 = unembed_term t2 in (uu____1002, uu____1003) in
             FStar_Reflection_Data.Tv_Abs uu____997
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1006)::(t2,uu____1008)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1043 =
               let uu____1048 = unembed_binder b in
               let uu____1049 = unembed_term t2 in (uu____1048, uu____1049) in
             FStar_Reflection_Data.Tv_Arrow uu____1043
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1052)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             (FStar_Syntax_Embeddings.unembed_unit u;
              FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1080)::(t2,uu____1082)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1117 =
               let uu____1122 = unembed_binder b in
               let uu____1123 = unembed_term t2 in (uu____1122, uu____1123) in
             FStar_Reflection_Data.Tv_Refine uu____1117
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1126)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1151 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1151
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1154)::(t2,uu____1156)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1191 =
               let uu____1196 = FStar_Syntax_Embeddings.unembed_int u in
               let uu____1197 = unembed_term t2 in (uu____1196, uu____1197) in
             FStar_Reflection_Data.Tv_Uvar uu____1191
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1200)::(brs,uu____1202)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1237 =
               let uu____1244 = unembed_term t2 in
               let uu____1245 =
                 FStar_Syntax_Embeddings.unembed_list unembed_branch brs in
               (uu____1244, uu____1245) in
             FStar_Reflection_Data.Tv_Match uu____1237
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1277 -> failwith "not an embedded term_view")
let rec last: 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____1304::xs -> last xs
let rec init: 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____1330 = init xs in x :: uu____1330
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1341 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1341
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1350 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1350
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____1360) ->
        let uu____1373 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____1373
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (bs,uu____1375) ->
        FStar_Reflection_Data.C_String (FStar_Util.string_of_bytes bs)
    | uu____1380 ->
        let uu____1381 =
          let uu____1382 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____1382 in
        failwith uu____1381
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1389 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1389
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1432 = last args in
        (match uu____1432 with
         | (a,uu____1446) ->
             let uu____1451 =
               let uu____1456 =
                 let uu____1459 =
                   let uu____1460 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1460 in
                 uu____1459 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos in
               (uu____1456, a) in
             FStar_Reflection_Data.Tv_App uu____1451)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1473,uu____1474) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1516 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1516 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1543 =
                    let uu____1548 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1548) in
                  FStar_Reflection_Data.Tv_Abs uu____1543))
    | FStar_Syntax_Syntax.Tm_type uu____1553 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1587 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1587 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1614 =
                    let uu____1619 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1619) in
                  FStar_Reflection_Data.Tv_Arrow uu____1614))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1635 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1635 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1664 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1674 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____1674
    | FStar_Syntax_Syntax.Tm_uvar (u,t2) ->
        let uu____1701 =
          let uu____1706 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____1706, t2) in
        FStar_Reflection_Data.Tv_Uvar uu____1701
    | FStar_Syntax_Syntax.Tm_match (t2,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____1756 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____1756
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____1775 =
                let uu____1782 =
                  FStar_List.map
                    (fun uu____1794  ->
                       match uu____1794 with
                       | (p1,uu____1802) -> inspect_pat p1) ps in
                (fv, uu____1782) in
              FStar_Reflection_Data.Pat_Cons uu____1775
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var
                (bv, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild
                (bv, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_dot_term uu____1815 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___80_1859  ->
               match uu___80_1859 with
               | (pat,uu____1881,t3) ->
                   let uu____1899 = inspect_pat pat in (uu____1899, t3)) brs1 in
        FStar_Reflection_Data.Tv_Match (t2, brs2)
    | uu____1912 ->
        ((let uu____1914 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1915 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1914 uu____1915);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____1921 =
          let uu____1932 = FStar_Util.string_of_int i in
          (uu____1932, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____1921
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string
          ((FStar_Util.bytes_of_string s), FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1951) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1955 =
          let uu____1964 = FStar_Syntax_Syntax.as_arg r in [uu____1964] in
        FStar_Syntax_Util.mk_app l uu____1955
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1969 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1969
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1973),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____1980 =
          let uu____1983 =
            let uu____1984 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____1984 in
          FStar_Syntax_Syntax.mk uu____1983 in
        uu____1980 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
              let uu____2007 =
                let uu____2008 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____2008 in
              FStar_All.pipe_left wrap uu____2007
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2017 =
                let uu____2018 =
                  let uu____2031 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2045 = pack_pat p1 in (uu____2045, false))
                      ps in
                  (fv, uu____2031) in
                FStar_Syntax_Syntax.Pat_cons uu____2018 in
              FStar_All.pipe_left wrap uu____2017
          | FStar_Reflection_Data.Pat_Var binder ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_var
                   (FStar_Pervasives_Native.fst binder))
          | FStar_Reflection_Data.Pat_Wild binder ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_wild
                   (FStar_Pervasives_Native.fst binder)) in
        let brs1 =
          FStar_List.map
            (fun uu___81_2091  ->
               match uu___81_2091 with
               | (pat,t1) ->
                   let uu____2108 = pack_pat pat in
                   (uu____2108, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | uu____2120 -> failwith "pack: unexpected term view"
let embed_order: FStar_Order.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Order.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2130 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2130 with
    | (hd1,args) ->
        let uu____2167 =
          let uu____2180 =
            let uu____2181 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2181.FStar_Syntax_Syntax.n in
          (uu____2180, args) in
        (match uu____2167 with
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
         | uu____2237 -> failwith "not an embedded order")
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
    let uu____2278 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2278 with
    | (hd1,args) ->
        let uu____2315 =
          let uu____2328 =
            let uu____2329 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2329.FStar_Syntax_Syntax.n in
          (uu____2328, args) in
        (match uu____2315 with
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
         | uu____2400 -> failwith "not an embedded norm_step")
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____2465,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____2566,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____2583 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____2583 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____2656,n1,uu____2658) ->
                          let uu____2663 =
                            let uu____2668 = FStar_Ident.path_of_lid lid2 in
                            (uu____2668, t1) in
                          FStar_Reflection_Data.Ctor uu____2663
                      | uu____2673 -> failwith "wat 1")
                 | uu____2674 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | uu____2702 -> FStar_Reflection_Data.Unk)
let embed_ctor: FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____2709 =
          let uu____2710 =
            let uu____2711 =
              let uu____2712 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2712 in
            let uu____2713 =
              let uu____2716 =
                let uu____2717 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____2717 in
              [uu____2716] in
            uu____2711 :: uu____2713 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____2710 in
        uu____2709 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2725 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2725 with
    | (hd1,args) ->
        let uu____2762 =
          let uu____2775 =
            let uu____2776 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2776.FStar_Syntax_Syntax.n in
          (uu____2775, args) in
        (match uu____2762 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2789)::(t2,uu____2791)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____2826 =
               let uu____2831 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____2834 = unembed_term t2 in (uu____2831, uu____2834) in
             FStar_Reflection_Data.Ctor uu____2826
         | uu____2837 -> failwith "not an embedded ctor")
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____2866 =
          let uu____2867 =
            let uu____2868 =
              let uu____2869 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____2869 in
            let uu____2870 =
              let uu____2873 =
                let uu____2874 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____2874 in
              let uu____2875 =
                let uu____2878 =
                  let uu____2879 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____2879 in
                let uu____2880 =
                  let uu____2883 =
                    let uu____2884 =
                      FStar_Syntax_Embeddings.embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____2884 in
                  [uu____2883] in
                uu____2878 :: uu____2880 in
              uu____2873 :: uu____2875 in
            uu____2868 :: uu____2870 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____2867 in
        uu____2866 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2892 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2892 with
    | (hd1,args) ->
        let uu____2929 =
          let uu____2942 =
            let uu____2943 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2943.FStar_Syntax_Syntax.n in
          (uu____2942, args) in
        (match uu____2929 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2956)::(bs,uu____2958)::(t2,uu____2960)::(dcs,uu____2962)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3017 =
               let uu____3030 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____3033 = unembed_binders bs in
               let uu____3036 = unembed_term t2 in
               let uu____3037 =
                 FStar_Syntax_Embeddings.unembed_list unembed_ctor dcs in
               (uu____3030, uu____3033, uu____3036, uu____3037) in
             FStar_Reflection_Data.Sg_Inductive uu____3017
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____3061 -> failwith "not an embedded sigelt_view")
let binders_of_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders
  = fun e  -> FStar_TypeChecker_Env.all_binders e
let type_of_binder: FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term =
  fun b  -> match b with | (b1,uu____3083) -> b1.FStar_Syntax_Syntax.sort
let term_eq:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool
  = FStar_Syntax_Util.term_eq
let fresh_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let uu____3098 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t in
    (uu____3098, FStar_Pervasives_Native.None)
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  FStar_Syntax_Print.term_to_string