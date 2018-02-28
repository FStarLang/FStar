open Prims
let (embed_binder :
  FStar_Range.range -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun b  ->
      FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_binder
        FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some rng)
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____19 =
      let uu____20 = FStar_Syntax_Subst.compress t  in
      uu____20.FStar_Syntax_Syntax.n  in
    match uu____19 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____26 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____26
    | uu____27 ->
        ((let uu____29 =
            let uu____34 =
              let uu____35 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____35  in
            (FStar_Errors.Warning_NotEmbedded, uu____34)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____29);
         FStar_Pervasives_Native.None)
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (embed_binders :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun l  ->
      let uu____48 =
        FStar_Syntax_Embeddings.embed_list embed_binder
          FStar_Reflection_Data.fstar_refl_binder
         in
      uu____48 rng l
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____63 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____63 t
  
let (embed_term :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  ->
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_meta
           (FStar_Syntax_Syntax.tun,
             (FStar_Syntax_Syntax.Meta_quoted (t, ()))))
        FStar_Pervasives_Native.None rng
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____89;
           FStar_Syntax_Syntax.pos = uu____90;
           FStar_Syntax_Syntax.vars = uu____91;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> FStar_Pervasives_Native.Some qt
    | uu____104 ->
        ((let uu____106 =
            let uu____111 =
              let uu____112 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____112  in
            (FStar_Errors.Warning_NotEmbedded, uu____111)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____106);
         FStar_Pervasives_Native.None)
  
let (embed_fvar :
  FStar_Range.range -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun fv  ->
      FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fvar
        FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng)
  
let (unembed_fvar :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____131 =
      let uu____132 = FStar_Syntax_Subst.compress t  in
      uu____132.FStar_Syntax_Syntax.n  in
    match uu____131 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____138 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____138
    | uu____139 ->
        ((let uu____141 =
            let uu____146 =
              let uu____147 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____147  in
            (FStar_Errors.Warning_NotEmbedded, uu____146)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____141);
         FStar_Pervasives_Native.None)
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (embed_comp :
  FStar_Range.range -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
        FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____169 =
      let uu____170 = FStar_Syntax_Subst.compress t  in
      uu____170.FStar_Syntax_Syntax.n  in
    match uu____169 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____176 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____176
    | uu____177 ->
        ((let uu____179 =
            let uu____184 =
              let uu____185 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____185  in
            (FStar_Errors.Warning_NotEmbedded, uu____184)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____179);
         FStar_Pervasives_Native.None)
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (embed_env :
  FStar_Range.range -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun e  ->
      FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
        FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____207 =
      let uu____208 = FStar_Syntax_Subst.compress t  in
      uu____208.FStar_Syntax_Syntax.n  in
    match uu____207 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____214 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____214
    | uu____215 ->
        ((let uu____217 =
            let uu____222 =
              let uu____223 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____223  in
            (FStar_Errors.Warning_NotEmbedded, uu____222)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____217);
         FStar_Pervasives_Native.None)
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (embed_const :
  FStar_Range.range ->
    FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      let r =
        match c with
        | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
        | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
        | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
        | FStar_Reflection_Data.C_Int i ->
            let uu____238 =
              let uu____239 =
                let uu____240 =
                  let uu____241 =
                    let uu____242 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____242  in
                  FStar_Syntax_Syntax.as_arg uu____241  in
                [uu____240]  in
              FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
                uu____239
               in
            uu____238 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____246 =
              let uu____247 =
                let uu____248 =
                  let uu____249 = FStar_Syntax_Embeddings.embed_string rng s
                     in
                  FStar_Syntax_Syntax.as_arg uu____249  in
                [uu____248]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String uu____247
               in
            uu____246 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___55_252 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_252.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_252.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____263 = FStar_Syntax_Util.head_and_args t1  in
    match uu____263 with
    | (hd1,args) ->
        let uu____302 =
          let uu____315 =
            let uu____316 = FStar_Syntax_Util.un_uinst hd1  in
            uu____316.FStar_Syntax_Syntax.n  in
          (uu____315, args)  in
        (match uu____302 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_True_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_False_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____376)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____401 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____401
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____410)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____435 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____435
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____442 ->
             ((let uu____456 =
                 let uu____461 =
                   let uu____462 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____462
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____461)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____456);
              FStar_Pervasives_Native.None))
  
let rec (embed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedder) =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____471 =
            let uu____472 =
              let uu____473 =
                let uu____474 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____474  in
              [uu____473]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant uu____472
             in
          uu____471 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____483 =
            let uu____484 =
              let uu____485 =
                let uu____486 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____486  in
              let uu____487 =
                let uu____490 =
                  let uu____491 =
                    let uu____492 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern
                       in
                    uu____492 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____491  in
                [uu____490]  in
              uu____485 :: uu____487  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
              uu____484
             in
          uu____483 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____503 =
            let uu____504 =
              let uu____505 =
                let uu____506 =
                  let uu____507 = FStar_Syntax_Syntax.mk_binder bv  in
                  embed_binder rng uu____507  in
                FStar_Syntax_Syntax.as_arg uu____506  in
              [uu____505]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
              uu____504
             in
          uu____503 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____511 =
            let uu____512 =
              let uu____513 =
                let uu____514 =
                  let uu____515 = FStar_Syntax_Syntax.mk_binder bv  in
                  embed_binder rng uu____515  in
                FStar_Syntax_Syntax.as_arg uu____514  in
              [uu____513]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
              uu____512
             in
          uu____511 FStar_Pervasives_Native.None rng
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____526 = FStar_Syntax_Util.head_and_args t1  in
    match uu____526 with
    | (hd1,args) ->
        let uu____565 =
          let uu____578 =
            let uu____579 = FStar_Syntax_Util.un_uinst hd1  in
            uu____579.FStar_Syntax_Syntax.n  in
          (uu____578, args)  in
        (match uu____565 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____594)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____619 = unembed_const c  in
             FStar_Util.bind_opt uu____619
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____628)::(ps,uu____630)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____665 = unembed_fvar f  in
             FStar_Util.bind_opt uu____665
               (fun f1  ->
                  let uu____671 =
                    let uu____676 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____676 ps  in
                  FStar_Util.bind_opt uu____671
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____695)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____720 = unembed_binder b  in
             FStar_Util.bind_opt uu____720
               (fun uu____726  ->
                  match uu____726 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                        (FStar_Reflection_Data.Pat_Var bv))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____735)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____760 = unembed_binder b  in
             FStar_Util.bind_opt uu____760
               (fun uu____766  ->
                  match uu____766 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                        (FStar_Reflection_Data.Pat_Wild bv))
         | uu____773 ->
             ((let uu____787 =
                 let uu____792 =
                   let uu____793 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s" uu____793
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____792)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____787);
              FStar_Pervasives_Native.None))
  
let (embed_branch :
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedder)
  =
  FStar_Syntax_Embeddings.embed_pair embed_pattern
    FStar_Reflection_Data.fstar_refl_pattern embed_term
    FStar_Syntax_Syntax.t_term
  
let (unembed_branch :
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_pair unembed_pattern unembed_term 
let (embed_aqualv :
  FStar_Range.range ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun q  ->
      let r =
        match q with
        | FStar_Reflection_Data.Q_Explicit  ->
            FStar_Reflection_Data.ref_Q_Explicit
        | FStar_Reflection_Data.Q_Implicit  ->
            FStar_Reflection_Data.ref_Q_Implicit
         in
      let uu___56_826 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___56_826.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___56_826.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____837 = FStar_Syntax_Util.head_and_args t1  in
    match uu____837 with
    | (hd1,args) ->
        let uu____876 =
          let uu____889 =
            let uu____890 = FStar_Syntax_Util.un_uinst hd1  in
            uu____890.FStar_Syntax_Syntax.n  in
          (uu____889, args)  in
        (match uu____876 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____933 ->
             ((let uu____947 =
                 let uu____952 =
                   let uu____953 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____953
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____952)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____947);
              FStar_Pervasives_Native.None))
  
let (embed_argv :
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedder)
  =
  FStar_Syntax_Embeddings.embed_pair embed_term FStar_Syntax_Syntax.t_term
    embed_aqualv FStar_Reflection_Data.fstar_refl_aqualv
  
let (unembed_argv :
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_pair unembed_term unembed_aqualv 
let (embed_term_view :
  FStar_Range.range ->
    FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  ->
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____986 =
            let uu____987 =
              let uu____988 =
                let uu____989 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____989  in
              [uu____988]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
              uu____987
             in
          uu____986 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____993 =
            let uu____994 =
              let uu____995 =
                let uu____996 = embed_binder rng bv  in
                FStar_Syntax_Syntax.as_arg uu____996  in
              [uu____995]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
              uu____994
             in
          uu____993 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1001 =
            let uu____1002 =
              let uu____1003 =
                let uu____1004 = embed_term rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1004  in
              let uu____1005 =
                let uu____1008 =
                  let uu____1009 = embed_argv rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1009  in
                [uu____1008]  in
              uu____1003 :: uu____1005  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
              uu____1002
             in
          uu____1001 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1014 =
            let uu____1015 =
              let uu____1016 =
                let uu____1017 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1017  in
              let uu____1018 =
                let uu____1021 =
                  let uu____1022 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1022  in
                [uu____1021]  in
              uu____1016 :: uu____1018  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
              uu____1015
             in
          uu____1014 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1027 =
            let uu____1028 =
              let uu____1029 =
                let uu____1030 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1030  in
              let uu____1031 =
                let uu____1034 =
                  let uu____1035 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____1035  in
                [uu____1034]  in
              uu____1029 :: uu____1031  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
              uu____1028
             in
          uu____1027 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1039 =
            let uu____1040 =
              let uu____1041 =
                let uu____1042 = FStar_Syntax_Embeddings.embed_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1042  in
              [uu____1041]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
              uu____1040
             in
          uu____1039 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1047 =
            let uu____1048 =
              let uu____1049 =
                let uu____1050 = embed_binder rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1050  in
              let uu____1051 =
                let uu____1054 =
                  let uu____1055 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1055  in
                [uu____1054]  in
              uu____1049 :: uu____1051  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
              uu____1048
             in
          uu____1047 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1059 =
            let uu____1060 =
              let uu____1061 =
                let uu____1062 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1062  in
              [uu____1061]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
              uu____1060
             in
          uu____1059 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1067 =
            let uu____1068 =
              let uu____1069 =
                let uu____1070 = FStar_Syntax_Embeddings.embed_int rng u  in
                FStar_Syntax_Syntax.as_arg uu____1070  in
              let uu____1071 =
                let uu____1074 =
                  let uu____1075 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1075  in
                [uu____1074]  in
              uu____1069 :: uu____1071  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
              uu____1068
             in
          uu____1067 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
          let uu____1081 =
            let uu____1082 =
              let uu____1083 =
                let uu____1084 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1084  in
              let uu____1085 =
                let uu____1088 =
                  let uu____1089 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1089  in
                let uu____1090 =
                  let uu____1093 =
                    let uu____1094 = embed_term rng t2  in
                    FStar_Syntax_Syntax.as_arg uu____1094  in
                  [uu____1093]  in
                uu____1088 :: uu____1090  in
              uu____1083 :: uu____1085  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let
              uu____1082
             in
          uu____1081 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1103 =
            let uu____1104 =
              let uu____1105 =
                let uu____1106 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____1106  in
              let uu____1107 =
                let uu____1110 =
                  let uu____1111 =
                    let uu____1112 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____1112 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____1111  in
                [uu____1110]  in
              uu____1105 :: uu____1107  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
              uu____1104
             in
          uu____1103 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___57_1130 = FStar_Reflection_Data.ref_Tv_Unknown  in
          {
            FStar_Syntax_Syntax.n = (uu___57_1130.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___57_1130.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_term_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1141 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1141 with
    | (hd1,args) ->
        let uu____1180 =
          let uu____1193 =
            let uu____1194 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1194.FStar_Syntax_Syntax.n  in
          (uu____1193, args)  in
        (match uu____1180 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1209)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1234 = unembed_binder b  in
             FStar_Util.bind_opt uu____1234
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1243)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1268 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1268
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1277)::(r,uu____1279)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1314 = unembed_term l  in
             FStar_Util.bind_opt uu____1314
               (fun l1  ->
                  let uu____1320 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1320
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1345)::(t2,uu____1347)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1382 = unembed_binder b  in
             FStar_Util.bind_opt uu____1382
               (fun b1  ->
                  let uu____1388 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1388
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1397)::(t2,uu____1399)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1434 = unembed_binder b  in
             FStar_Util.bind_opt uu____1434
               (fun b1  ->
                  let uu____1440 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1440
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1449)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             let uu____1474 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1474
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1483)::(t2,uu____1485)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1520 = unembed_binder b  in
             FStar_Util.bind_opt uu____1520
               (fun b1  ->
                  let uu____1526 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1526
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1535)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1560 = unembed_const c  in
             FStar_Util.bind_opt uu____1560
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1569)::(t2,uu____1571)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1606 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1606
               (fun u1  ->
                  let uu____1612 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1612
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1621)::(t11,uu____1623)::(t2,uu____1625)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let_lid
             ->
             let uu____1670 = unembed_binder b  in
             FStar_Util.bind_opt uu____1670
               (fun b1  ->
                  let uu____1676 = unembed_term t11  in
                  FStar_Util.bind_opt uu____1676
                    (fun t12  ->
                       let uu____1682 = unembed_term t2  in
                       FStar_Util.bind_opt uu____1682
                         (fun t21  ->
                            FStar_All.pipe_left
                              (fun _0_55  ->
                                 FStar_Pervasives_Native.Some _0_55)
                              (FStar_Reflection_Data.Tv_Let (b1, t12, t21)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1691)::(brs,uu____1693)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1728 = unembed_term t2  in
             FStar_Util.bind_opt uu____1728
               (fun t3  ->
                  let uu____1734 =
                    let uu____1743 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____1743 brs  in
                  FStar_Util.bind_opt uu____1734
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_56  -> FStar_Pervasives_Native.Some _0_56)
                         (FStar_Reflection_Data.Tv_Match (t3, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             ->
             FStar_All.pipe_left
               (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
               FStar_Reflection_Data.Tv_Unknown
         | uu____1797 ->
             ((let uu____1811 =
                 let uu____1816 =
                   let uu____1817 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____1817
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1816)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1811);
              FStar_Pervasives_Native.None))
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____1828 =
            let uu____1829 =
              let uu____1830 =
                let uu____1831 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____1831  in
              [uu____1830]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Total
              uu____1829
             in
          uu____1828 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____1839 =
            let uu____1840 =
              let uu____1841 =
                let uu____1842 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____1842  in
              let uu____1843 =
                let uu____1846 =
                  let uu____1847 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____1847  in
                [uu____1846]  in
              uu____1841 :: uu____1843  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Lemma
              uu____1840
             in
          uu____1839 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___58_1850 = FStar_Reflection_Data.ref_C_Unknown  in
          {
            FStar_Syntax_Syntax.n = (uu___58_1850.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___58_1850.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1861 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1861 with
    | (hd1,args) ->
        let uu____1900 =
          let uu____1913 =
            let uu____1914 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1914.FStar_Syntax_Syntax.n  in
          (uu____1913, args)  in
        (match uu____1900 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____1929)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total_lid
             ->
             let uu____1954 = unembed_term t2  in
             FStar_Util.bind_opt uu____1954
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____1963)::(post,uu____1965)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma_lid
             ->
             let uu____2000 = unembed_term pre  in
             FStar_Util.bind_opt uu____2000
               (fun pre1  ->
                  let uu____2006 = unembed_term post  in
                  FStar_Util.bind_opt uu____2006
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_59  -> FStar_Pervasives_Native.Some _0_59)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown_lid
             ->
             FStar_All.pipe_left
               (fun _0_60  -> FStar_Pervasives_Native.Some _0_60)
               FStar_Reflection_Data.C_Unknown
         | uu____2030 ->
             ((let uu____2044 =
                 let uu____2049 =
                   let uu____2050 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2050
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2049)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2044);
              FStar_Pervasives_Native.None))
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____2064::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____2089 = init xs  in x :: uu____2089
  
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv  ->
    let uu____2099 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____2099
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let uu____2107 = FStar_Parser_Const.p2l ns  in
    FStar_Syntax_Syntax.lid_as_fv uu____2107
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
  
let (inspect_bv : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b) 
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2115) ->
        let uu____2128 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____2128
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____2130) ->
        FStar_Reflection_Data.C_String s
    | uu____2131 ->
        let uu____2132 =
          let uu____2133 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____2133  in
        failwith uu____2132
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____2140) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2146 = FStar_Syntax_Syntax.mk_binder bv  in
        FStar_Reflection_Data.Tv_Var uu____2146
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2189 = last args  in
        (match uu____2189 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____2209) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit
                in
             let uu____2210 =
               let uu____2215 =
                 let uu____2218 =
                   let uu____2219 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2219  in
                 uu____2218 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos
                  in
               (uu____2215, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____2210)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2238,uu____2239) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____2281 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____2281 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2308 =
                    let uu____2313 = FStar_Syntax_Util.abs bs2 t4 k  in
                    (b, uu____2313)  in
                  FStar_Reflection_Data.Tv_Abs uu____2308))
    | FStar_Syntax_Syntax.Tm_type uu____2318 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____2334 ->
        let uu____2347 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____2347 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____2371 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____2371 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2400 -> failwith "impossible"  in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2410 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____2410
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2437 =
          let uu____2442 =
            let uu____2443 = FStar_Syntax_Unionfind.uvar_id u  in
            FStar_BigInt.of_int_fs uu____2443  in
          (uu____2442, t3)  in
        FStar_Reflection_Data.Tv_Uvar uu____2437
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2463 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____2466 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____2466 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2495 ->
                          failwith
                            "impossible: open_term returned different amount of binders"
                       in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2553 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____2553
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2572 =
                let uu____2579 =
                  FStar_List.map
                    (fun uu____2591  ->
                       match uu____2591 with
                       | (p1,uu____2599) -> inspect_pat p1) ps
                   in
                (fv, uu____2579)  in
              FStar_Reflection_Data.Pat_Cons uu____2572
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2608 ->
              failwith "NYI: Pat_dot_term"
           in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
        let brs2 =
          FStar_List.map
            (fun uu___53_2652  ->
               match uu___53_2652 with
               | (pat,uu____2674,t4) ->
                   let uu____2692 = inspect_pat pat  in (uu____2692, t4))
            brs1
           in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2705 ->
        ((let uu____2707 =
            let uu____2712 =
              let uu____2713 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____2714 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____2713
                uu____2714
               in
            (FStar_Errors.Warning_CantInspect, uu____2712)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____2707);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2719) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2730)::(post,uu____2732)::uu____2733 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2766 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2776 ->
        FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2789 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2794 =
          let uu____2805 = FStar_BigInt.string_of_big_int i  in
          (uu____2805, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____2794
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2821) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2830 =
               let uu____2839 = FStar_Syntax_Syntax.as_arg r  in [uu____2839]
                in
             FStar_Syntax_Util.mk_app l uu____2830
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2840 =
               let uu____2849 = FStar_Syntax_Syntax.iarg r  in [uu____2849]
                in
             FStar_Syntax_Util.mk_app l uu____2840)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2855),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2862 =
          let uu____2865 =
            let uu____2866 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____2866  in
          FStar_Syntax_Syntax.mk uu____2865  in
        uu____2862 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____2872 = FStar_BigInt.to_int_fs u  in
        FStar_Syntax_Util.uvar_from_id uu____2872 t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b  in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            []
           in
        let uu____2880 =
          let uu____2883 =
            let uu____2884 =
              let uu____2897 = FStar_Syntax_Subst.close [b] t2  in
              ((false, [lb]), uu____2897)  in
            FStar_Syntax_Syntax.Tm_let uu____2884  in
          FStar_Syntax_Syntax.mk uu____2883  in
        uu____2880 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2926 =
                let uu____2927 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____2927  in
              FStar_All.pipe_left wrap uu____2926
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2936 =
                let uu____2937 =
                  let uu____2950 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2964 = pack_pat p1  in (uu____2964, false))
                      ps
                     in
                  (fv, uu____2950)  in
                FStar_Syntax_Syntax.Pat_cons uu____2937  in
              FStar_All.pipe_left wrap uu____2936
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
           in
        let brs1 =
          FStar_List.map
            (fun uu___54_3010  ->
               match uu___54_3010 with
               | (pat,t1) ->
                   let uu____3027 = pack_pat pat  in
                   (uu____3027, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        failwith "pack: unexpected term view"
  
let (embed_order :
  FStar_Range.range -> FStar_Order.order -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun o  ->
      let r =
        match o with
        | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
        | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
        | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt  in
      let uu___59_3049 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___59_3049.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___59_3049.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3060 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3060 with
    | (hd1,args) ->
        let uu____3099 =
          let uu____3112 =
            let uu____3113 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3113.FStar_Syntax_Syntax.n  in
          (uu____3112, args)  in
        (match uu____3099 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Lt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Eq_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Gt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Gt
         | uu____3171 ->
             ((let uu____3185 =
                 let uu____3190 =
                   let uu____3191 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____3191
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3190)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3185);
              FStar_Pervasives_Native.None))
  
let (compare_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Order.order)
  =
  fun x  ->
    fun y  ->
      let n1 =
        FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x)
          (FStar_Pervasives_Native.fst y)
         in
      if n1 < (Prims.parse_int "0")
      then FStar_Order.Lt
      else
        if n1 = (Prims.parse_int "0") then FStar_Order.Eq else FStar_Order.Gt
  
let (is_free :
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun x  ->
    fun t  -> FStar_Syntax_Util.is_free_in (FStar_Pervasives_Native.fst x) t
  
let (lookup_typ :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list -> FStar_Reflection_Data.sigelt_view)
  =
  fun env  ->
    fun ns  ->
      let lid = FStar_Parser_Const.p2l ns  in
      let res = FStar_TypeChecker_Env.lookup_qname env lid  in
      match res with
      | FStar_Pervasives_Native.None  -> FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____3237,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____3338,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1  in
               let ctor1 dc_lid =
                 let uu____3355 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid  in
                 match uu____3355 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3408,n1,uu____3410) ->
                          let uu____3415 =
                            let uu____3420 = FStar_Ident.path_of_lid lid2  in
                            (uu____3420, t1)  in
                          FStar_Reflection_Data.Ctor uu____3415
                      | uu____3425 -> failwith "wat 1")
                 | uu____3426 -> failwith "wat 2"  in
               let ctors = FStar_List.map ctor1 dc_lids  in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3435) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____3450 ->
                     failwith "global Sig_let has bv"
                  in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____3455 -> FStar_Reflection_Data.Unk)
  
let (embed_ctor :
  FStar_Range.range -> FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      match c with
      | FStar_Reflection_Data.Ctor (nm,t) ->
          let uu____3467 =
            let uu____3468 =
              let uu____3469 =
                let uu____3470 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____3470  in
              let uu____3471 =
                let uu____3474 =
                  let uu____3475 = embed_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____3475  in
                [uu____3474]  in
              uu____3469 :: uu____3471  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
              uu____3468
             in
          uu____3467 FStar_Pervasives_Native.None rng
  
let (unembed_ctor :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.ctor FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3488 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3488 with
    | (hd1,args) ->
        let uu____3527 =
          let uu____3540 =
            let uu____3541 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3541.FStar_Syntax_Syntax.n  in
          (uu____3540, args)  in
        (match uu____3527 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3556)::(t2,uu____3558)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3593 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3593
               (fun nm1  ->
                  let uu____3605 = unembed_term t2  in
                  FStar_Util.bind_opt uu____3605
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.Ctor (nm1, t3))))
         | uu____3614 ->
             ((let uu____3628 =
                 let uu____3633 =
                   let uu____3634 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded ctor: %s" uu____3634
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3633)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3628);
              FStar_Pervasives_Native.None))
  
let (embed_sigelt_view :
  FStar_Range.range ->
    FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun sev  ->
      match sev with
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____3656 =
            let uu____3657 =
              let uu____3658 =
                let uu____3659 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____3659  in
              let uu____3660 =
                let uu____3663 =
                  let uu____3664 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____3664  in
                let uu____3665 =
                  let uu____3668 =
                    let uu____3669 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3669  in
                  let uu____3670 =
                    let uu____3673 =
                      let uu____3674 =
                        let uu____3675 =
                          FStar_Syntax_Embeddings.embed_list embed_ctor
                            FStar_Reflection_Data.fstar_refl_ctor
                           in
                        uu____3675 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____3674  in
                    [uu____3673]  in
                  uu____3668 :: uu____3670  in
                uu____3663 :: uu____3665  in
              uu____3658 :: uu____3660  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive uu____3657
             in
          uu____3656 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
          let uu____3688 =
            let uu____3689 =
              let uu____3690 =
                let uu____3691 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____3691  in
              let uu____3692 =
                let uu____3695 =
                  let uu____3696 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3696  in
                let uu____3697 =
                  let uu____3700 =
                    let uu____3701 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3701  in
                  [uu____3700]  in
                uu____3695 :: uu____3697  in
              uu____3690 :: uu____3692  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Let
              uu____3689
             in
          uu____3688 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___60_3704 = FStar_Reflection_Data.ref_Unk  in
          {
            FStar_Syntax_Syntax.n = (uu___60_3704.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___60_3704.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3715 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3715 with
    | (hd1,args) ->
        let uu____3754 =
          let uu____3767 =
            let uu____3768 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3768.FStar_Syntax_Syntax.n  in
          (uu____3767, args)  in
        (match uu____3754 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3783)::(bs,uu____3785)::(t2,uu____3787)::(dcs,uu____3789)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3844 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3844
               (fun nm1  ->
                  let uu____3856 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____3856
                    (fun bs1  ->
                       let uu____3862 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3862
                         (fun t3  ->
                            let uu____3868 =
                              let uu____3873 =
                                FStar_Syntax_Embeddings.unembed_list
                                  unembed_ctor
                                 in
                              uu____3873 dcs  in
                            FStar_Util.bind_opt uu____3868
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____3894)::(ty,uu____3896)::(t2,uu____3898)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let_lid
             ->
             let uu____3943 = unembed_fvar fvar1  in
             FStar_Util.bind_opt uu____3943
               (fun fvar2  ->
                  let uu____3949 = unembed_term ty  in
                  FStar_Util.bind_opt uu____3949
                    (fun ty1  ->
                       let uu____3955 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3955
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_63  ->
                                 FStar_Pervasives_Native.Some _0_63)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____3977 ->
             ((let uu____3991 =
                 let uu____3996 =
                   let uu____3997 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____3997
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3996)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3991);
              FStar_Pervasives_Native.None))
  
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (type_of_binder : FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.typ)
  = fun b  -> match b with | (b1,uu____4005) -> b1.FStar_Syntax_Syntax.sort 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____4012 = FStar_Syntax_Util.un_uinst t1  in
      let uu____4013 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____4012 uu____4013
  
let (fresh_binder : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.binder) =
  fun t  ->
    let uu____4017 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t  in
    (uu____4017, FStar_Pervasives_Native.None)
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 