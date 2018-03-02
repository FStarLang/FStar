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
  
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv  ->
    let uu____120 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____120
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let uu____128 = FStar_Parser_Const.p2l ns  in
    FStar_Syntax_Syntax.lid_as_fv uu____128
      (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "999"))
      FStar_Pervasives_Native.None
  
let (embed_fvar :
  FStar_Range.range -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun fv  ->
      FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
        FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng)
  
let (unembed_fvar :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____147 =
      let uu____148 = FStar_Syntax_Subst.compress t  in
      uu____148.FStar_Syntax_Syntax.n  in
    match uu____147 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____154 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____154
    | uu____155 ->
        ((let uu____157 =
            let uu____162 =
              let uu____163 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____163  in
            (FStar_Errors.Warning_NotEmbedded, uu____162)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____157);
         FStar_Pervasives_Native.None)
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____168 =
      let uu____169 =
        let uu____170 =
          let uu____171 =
            let uu____172 = inspect_fv fv  in
            let uu____175 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____175 i.FStar_Syntax_Syntax.rng uu____172  in
          FStar_Syntax_Syntax.as_arg uu____171  in
        [uu____170]  in
      FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv
        uu____169
       in
    uu____168 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
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
    let uu____203 =
      let uu____204 = FStar_Syntax_Subst.compress t  in
      uu____204.FStar_Syntax_Syntax.n  in
    match uu____203 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____210 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____210
    | uu____211 ->
        ((let uu____213 =
            let uu____218 =
              let uu____219 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____219  in
            (FStar_Errors.Warning_NotEmbedded, uu____218)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____213);
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
    let uu____241 =
      let uu____242 = FStar_Syntax_Subst.compress t  in
      uu____242.FStar_Syntax_Syntax.n  in
    match uu____241 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____248 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____248
    | uu____249 ->
        ((let uu____251 =
            let uu____256 =
              let uu____257 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____257  in
            (FStar_Errors.Warning_NotEmbedded, uu____256)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____251);
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
        | FStar_Reflection_Data.C_Unit  ->
            FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.t
        | FStar_Reflection_Data.C_True  ->
            FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.t
        | FStar_Reflection_Data.C_False  ->
            FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.t
        | FStar_Reflection_Data.C_Int i ->
            let uu____272 =
              let uu____273 =
                let uu____274 =
                  let uu____275 =
                    let uu____276 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____276  in
                  FStar_Syntax_Syntax.as_arg uu____275  in
                [uu____274]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
                uu____273
               in
            uu____272 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____280 =
              let uu____281 =
                let uu____282 =
                  let uu____283 = FStar_Syntax_Embeddings.embed_string rng s
                     in
                  FStar_Syntax_Syntax.as_arg uu____283  in
                [uu____282]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
                uu____281
               in
            uu____280 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___55_286 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_286.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_286.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____297 = FStar_Syntax_Util.head_and_args t1  in
    match uu____297 with
    | (hd1,args) ->
        let uu____336 =
          let uu____349 =
            let uu____350 = FStar_Syntax_Util.un_uinst hd1  in
            uu____350.FStar_Syntax_Syntax.n  in
          (uu____349, args)  in
        (match uu____336 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____410)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____435 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____435
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____444)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____469 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____469
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____476 ->
             ((let uu____490 =
                 let uu____495 =
                   let uu____496 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____496
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____495)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____490);
              FStar_Pervasives_Native.None))
  
let rec (embed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedder) =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____505 =
            let uu____506 =
              let uu____507 =
                let uu____508 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____508  in
              [uu____507]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____506
             in
          uu____505 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____517 =
            let uu____518 =
              let uu____519 =
                let uu____520 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____520  in
              let uu____521 =
                let uu____524 =
                  let uu____525 =
                    let uu____526 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern
                       in
                    uu____526 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____525  in
                [uu____524]  in
              uu____519 :: uu____521  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____518
             in
          uu____517 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____537 =
            let uu____538 =
              let uu____539 =
                let uu____540 =
                  let uu____541 = FStar_Syntax_Syntax.mk_binder bv  in
                  embed_binder rng uu____541  in
                FStar_Syntax_Syntax.as_arg uu____540  in
              [uu____539]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____538
             in
          uu____537 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____545 =
            let uu____546 =
              let uu____547 =
                let uu____548 =
                  let uu____549 = FStar_Syntax_Syntax.mk_binder bv  in
                  embed_binder rng uu____549  in
                FStar_Syntax_Syntax.as_arg uu____548  in
              [uu____547]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____546
             in
          uu____545 FStar_Pervasives_Native.None rng
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____560 = FStar_Syntax_Util.head_and_args t1  in
    match uu____560 with
    | (hd1,args) ->
        let uu____599 =
          let uu____612 =
            let uu____613 = FStar_Syntax_Util.un_uinst hd1  in
            uu____613.FStar_Syntax_Syntax.n  in
          (uu____612, args)  in
        (match uu____599 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____628)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____653 = unembed_const c  in
             FStar_Util.bind_opt uu____653
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____662)::(ps,uu____664)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____699 = unembed_fvar f  in
             FStar_Util.bind_opt uu____699
               (fun f1  ->
                  let uu____705 =
                    let uu____710 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____710 ps  in
                  FStar_Util.bind_opt uu____705
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____729)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____754 = unembed_binder b  in
             FStar_Util.bind_opt uu____754
               (fun uu____760  ->
                  match uu____760 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                        (FStar_Reflection_Data.Pat_Var bv))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____769)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____794 = unembed_binder b  in
             FStar_Util.bind_opt uu____794
               (fun uu____800  ->
                  match uu____800 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                        (FStar_Reflection_Data.Pat_Wild bv))
         | uu____807 ->
             ((let uu____821 =
                 let uu____826 =
                   let uu____827 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s" uu____827
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____826)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____821);
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
            FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.t
        | FStar_Reflection_Data.Q_Implicit  ->
            FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.t
         in
      let uu___56_860 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___56_860.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___56_860.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____871 = FStar_Syntax_Util.head_and_args t1  in
    match uu____871 with
    | (hd1,args) ->
        let uu____910 =
          let uu____923 =
            let uu____924 = FStar_Syntax_Util.un_uinst hd1  in
            uu____924.FStar_Syntax_Syntax.n  in
          (uu____923, args)  in
        (match uu____910 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____967 ->
             ((let uu____981 =
                 let uu____986 =
                   let uu____987 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____987
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____986)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____981);
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
          let uu____1020 =
            let uu____1021 =
              let uu____1022 =
                let uu____1023 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1023  in
              [uu____1022]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1021
             in
          uu____1020 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1027 =
            let uu____1028 =
              let uu____1029 =
                let uu____1030 = embed_binder rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1030  in
              [uu____1029]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1028
             in
          uu____1027 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1035 =
            let uu____1036 =
              let uu____1037 =
                let uu____1038 = embed_term rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1038  in
              let uu____1039 =
                let uu____1042 =
                  let uu____1043 = embed_argv rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1043  in
                [uu____1042]  in
              uu____1037 :: uu____1039  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1036
             in
          uu____1035 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1048 =
            let uu____1049 =
              let uu____1050 =
                let uu____1051 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1051  in
              let uu____1052 =
                let uu____1055 =
                  let uu____1056 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1056  in
                [uu____1055]  in
              uu____1050 :: uu____1052  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1049
             in
          uu____1048 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1061 =
            let uu____1062 =
              let uu____1063 =
                let uu____1064 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1064  in
              let uu____1065 =
                let uu____1068 =
                  let uu____1069 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____1069  in
                [uu____1068]  in
              uu____1063 :: uu____1065  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____1062
             in
          uu____1061 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1073 =
            let uu____1074 =
              let uu____1075 =
                let uu____1076 = FStar_Syntax_Embeddings.embed_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1076  in
              [uu____1075]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____1074
             in
          uu____1073 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1081 =
            let uu____1082 =
              let uu____1083 =
                let uu____1084 = embed_binder rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1084  in
              let uu____1085 =
                let uu____1088 =
                  let uu____1089 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1089  in
                [uu____1088]  in
              uu____1083 :: uu____1085  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____1082
             in
          uu____1081 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1093 =
            let uu____1094 =
              let uu____1095 =
                let uu____1096 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1096  in
              [uu____1095]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____1094
             in
          uu____1093 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1101 =
            let uu____1102 =
              let uu____1103 =
                let uu____1104 = FStar_Syntax_Embeddings.embed_int rng u  in
                FStar_Syntax_Syntax.as_arg uu____1104  in
              let uu____1105 =
                let uu____1108 =
                  let uu____1109 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1109  in
                [uu____1108]  in
              uu____1103 :: uu____1105  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____1102
             in
          uu____1101 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
          let uu____1115 =
            let uu____1116 =
              let uu____1117 =
                let uu____1118 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1118  in
              let uu____1119 =
                let uu____1122 =
                  let uu____1123 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1123  in
                let uu____1124 =
                  let uu____1127 =
                    let uu____1128 = embed_term rng t2  in
                    FStar_Syntax_Syntax.as_arg uu____1128  in
                  [uu____1127]  in
                uu____1122 :: uu____1124  in
              uu____1117 :: uu____1119  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____1116
             in
          uu____1115 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1137 =
            let uu____1138 =
              let uu____1139 =
                let uu____1140 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____1140  in
              let uu____1141 =
                let uu____1144 =
                  let uu____1145 =
                    let uu____1146 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____1146 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____1145  in
                [uu____1144]  in
              uu____1139 :: uu____1141  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____1138
             in
          uu____1137 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___57_1164 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___57_1164.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___57_1164.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_term_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1175 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1175 with
    | (hd1,args) ->
        let uu____1214 =
          let uu____1227 =
            let uu____1228 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1228.FStar_Syntax_Syntax.n  in
          (uu____1227, args)  in
        (match uu____1214 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1243)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1268 = unembed_binder b  in
             FStar_Util.bind_opt uu____1268
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1277)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1302 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1302
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1311)::(r,uu____1313)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1348 = unembed_term l  in
             FStar_Util.bind_opt uu____1348
               (fun l1  ->
                  let uu____1354 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1354
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1379)::(t2,uu____1381)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1416 = unembed_binder b  in
             FStar_Util.bind_opt uu____1416
               (fun b1  ->
                  let uu____1422 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1422
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1431)::(t2,uu____1433)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1468 = unembed_binder b  in
             FStar_Util.bind_opt uu____1468
               (fun b1  ->
                  let uu____1474 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1474
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1483)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1508 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1508
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1517)::(t2,uu____1519)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1554 = unembed_binder b  in
             FStar_Util.bind_opt uu____1554
               (fun b1  ->
                  let uu____1560 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1560
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1569)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1594 = unembed_const c  in
             FStar_Util.bind_opt uu____1594
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1603)::(t2,uu____1605)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1640 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1640
               (fun u1  ->
                  let uu____1646 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1646
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1655)::(t11,uu____1657)::(t2,uu____1659)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____1704 = unembed_binder b  in
             FStar_Util.bind_opt uu____1704
               (fun b1  ->
                  let uu____1710 = unembed_term t11  in
                  FStar_Util.bind_opt uu____1710
                    (fun t12  ->
                       let uu____1716 = unembed_term t2  in
                       FStar_Util.bind_opt uu____1716
                         (fun t21  ->
                            FStar_All.pipe_left
                              (fun _0_55  ->
                                 FStar_Pervasives_Native.Some _0_55)
                              (FStar_Reflection_Data.Tv_Let (b1, t12, t21)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1725)::(brs,uu____1727)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____1762 = unembed_term t2  in
             FStar_Util.bind_opt uu____1762
               (fun t3  ->
                  let uu____1768 =
                    let uu____1777 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____1777 brs  in
                  FStar_Util.bind_opt uu____1768
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_56  -> FStar_Pervasives_Native.Some _0_56)
                         (FStar_Reflection_Data.Tv_Match (t3, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
               FStar_Reflection_Data.Tv_Unknown
         | uu____1831 ->
             ((let uu____1845 =
                 let uu____1850 =
                   let uu____1851 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____1851
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1850)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1845);
              FStar_Pervasives_Native.None))
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____1862 =
            let uu____1863 =
              let uu____1864 =
                let uu____1865 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____1865  in
              [uu____1864]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____1863
             in
          uu____1862 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____1873 =
            let uu____1874 =
              let uu____1875 =
                let uu____1876 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____1876  in
              let uu____1877 =
                let uu____1880 =
                  let uu____1881 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____1881  in
                [uu____1880]  in
              uu____1875 :: uu____1877  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____1874
             in
          uu____1873 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___58_1884 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___58_1884.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___58_1884.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1895 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1895 with
    | (hd1,args) ->
        let uu____1934 =
          let uu____1947 =
            let uu____1948 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1948.FStar_Syntax_Syntax.n  in
          (uu____1947, args)  in
        (match uu____1934 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____1963)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____1988 = unembed_term t2  in
             FStar_Util.bind_opt uu____1988
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____1997)::(post,uu____1999)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2034 = unembed_term pre  in
             FStar_Util.bind_opt uu____2034
               (fun pre1  ->
                  let uu____2040 = unembed_term post  in
                  FStar_Util.bind_opt uu____2040
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_59  -> FStar_Pervasives_Native.Some _0_59)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_60  -> FStar_Pervasives_Native.Some _0_60)
               FStar_Reflection_Data.C_Unknown
         | uu____2064 ->
             ((let uu____2078 =
                 let uu____2083 =
                   let uu____2084 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2084
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2083)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2078);
              FStar_Pervasives_Native.None))
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____2098::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____2123 = init xs  in x :: uu____2123
  
let (inspect_bv : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b) 
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2133) ->
        let uu____2146 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____2146
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____2148) ->
        FStar_Reflection_Data.C_String s
    | uu____2149 ->
        let uu____2150 =
          let uu____2151 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____2151  in
        failwith uu____2150
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____2158) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2164 = FStar_Syntax_Syntax.mk_binder bv  in
        FStar_Reflection_Data.Tv_Var uu____2164
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2207 = last args  in
        (match uu____2207 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____2227) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit
                in
             let uu____2228 =
               let uu____2233 =
                 let uu____2236 =
                   let uu____2237 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2237  in
                 uu____2236 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos
                  in
               (uu____2233, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____2228)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2256,uu____2257) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____2299 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____2299 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2326 =
                    let uu____2331 = FStar_Syntax_Util.abs bs2 t4 k  in
                    (b, uu____2331)  in
                  FStar_Reflection_Data.Tv_Abs uu____2326))
    | FStar_Syntax_Syntax.Tm_type uu____2336 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____2352 ->
        let uu____2365 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____2365 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____2389 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____2389 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2418 -> failwith "impossible"  in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2428 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____2428
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2455 =
          let uu____2460 =
            let uu____2461 = FStar_Syntax_Unionfind.uvar_id u  in
            FStar_BigInt.of_int_fs uu____2461  in
          (uu____2460, t3)  in
        FStar_Reflection_Data.Tv_Uvar uu____2455
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2481 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____2484 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____2484 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2513 ->
                          failwith
                            "impossible: open_term returned different amount of binders"
                       in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2571 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____2571
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2590 =
                let uu____2597 =
                  FStar_List.map
                    (fun uu____2609  ->
                       match uu____2609 with
                       | (p1,uu____2617) -> inspect_pat p1) ps
                   in
                (fv, uu____2597)  in
              FStar_Reflection_Data.Pat_Cons uu____2590
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2626 ->
              failwith "NYI: Pat_dot_term"
           in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
        let brs2 =
          FStar_List.map
            (fun uu___53_2670  ->
               match uu___53_2670 with
               | (pat,uu____2692,t4) ->
                   let uu____2710 = inspect_pat pat  in (uu____2710, t4))
            brs1
           in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2723 ->
        ((let uu____2725 =
            let uu____2730 =
              let uu____2731 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____2732 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____2731
                uu____2732
               in
            (FStar_Errors.Warning_CantInspect, uu____2730)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____2725);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2737) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2748)::(post,uu____2750)::uu____2751 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2784 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2794 ->
        FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2807 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2812 =
          let uu____2823 = FStar_BigInt.string_of_big_int i  in
          (uu____2823, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____2812
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2839) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2848 =
               let uu____2857 = FStar_Syntax_Syntax.as_arg r  in [uu____2857]
                in
             FStar_Syntax_Util.mk_app l uu____2848
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2858 =
               let uu____2867 = FStar_Syntax_Syntax.iarg r  in [uu____2867]
                in
             FStar_Syntax_Util.mk_app l uu____2858)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2873),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2880 =
          let uu____2883 =
            let uu____2884 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____2884  in
          FStar_Syntax_Syntax.mk uu____2883  in
        uu____2880 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____2890 = FStar_BigInt.to_int_fs u  in
        FStar_Syntax_Util.uvar_from_id uu____2890 t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b  in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            []
           in
        let uu____2898 =
          let uu____2901 =
            let uu____2902 =
              let uu____2915 = FStar_Syntax_Subst.close [b] t2  in
              ((false, [lb]), uu____2915)  in
            FStar_Syntax_Syntax.Tm_let uu____2902  in
          FStar_Syntax_Syntax.mk uu____2901  in
        uu____2898 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2944 =
                let uu____2945 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____2945  in
              FStar_All.pipe_left wrap uu____2944
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2954 =
                let uu____2955 =
                  let uu____2968 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2982 = pack_pat p1  in (uu____2982, false))
                      ps
                     in
                  (fv, uu____2968)  in
                FStar_Syntax_Syntax.Pat_cons uu____2955  in
              FStar_All.pipe_left wrap uu____2954
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
           in
        let brs1 =
          FStar_List.map
            (fun uu___54_3028  ->
               match uu___54_3028 with
               | (pat,t1) ->
                   let uu____3045 = pack_pat pat  in
                   (uu____3045, FStar_Pervasives_Native.None, t1)) brs
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
      let uu___59_3067 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___59_3067.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___59_3067.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3078 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3078 with
    | (hd1,args) ->
        let uu____3117 =
          let uu____3130 =
            let uu____3131 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3131.FStar_Syntax_Syntax.n  in
          (uu____3130, args)  in
        (match uu____3117 with
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
         | uu____3189 ->
             ((let uu____3203 =
                 let uu____3208 =
                   let uu____3209 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____3209
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3208)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3203);
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____3255,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____3356,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1  in
               let ctor1 dc_lid =
                 let uu____3373 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid  in
                 match uu____3373 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3426,n1,uu____3428) ->
                          let uu____3433 =
                            let uu____3438 = FStar_Ident.path_of_lid lid2  in
                            (uu____3438, t1)  in
                          FStar_Reflection_Data.Ctor uu____3433
                      | uu____3443 -> failwith "wat 1")
                 | uu____3444 -> failwith "wat 2"  in
               let ctors = FStar_List.map ctor1 dc_lids  in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3453) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____3468 ->
                     failwith "global Sig_let has bv"
                  in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____3473 -> FStar_Reflection_Data.Unk)
  
let (embed_ctor :
  FStar_Range.range -> FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      match c with
      | FStar_Reflection_Data.Ctor (nm,t) ->
          let uu____3485 =
            let uu____3486 =
              let uu____3487 =
                let uu____3488 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____3488  in
              let uu____3489 =
                let uu____3492 =
                  let uu____3493 = embed_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____3493  in
                [uu____3492]  in
              uu____3487 :: uu____3489  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Ctor.FStar_Reflection_Data.t
              uu____3486
             in
          uu____3485 FStar_Pervasives_Native.None rng
  
let (unembed_ctor :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.ctor FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3506 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3506 with
    | (hd1,args) ->
        let uu____3545 =
          let uu____3558 =
            let uu____3559 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3559.FStar_Syntax_Syntax.n  in
          (uu____3558, args)  in
        (match uu____3545 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3574)::(t2,uu____3576)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor.FStar_Reflection_Data.lid
             ->
             let uu____3611 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3611
               (fun nm1  ->
                  let uu____3623 = unembed_term t2  in
                  FStar_Util.bind_opt uu____3623
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.Ctor (nm1, t3))))
         | uu____3632 ->
             ((let uu____3646 =
                 let uu____3651 =
                   let uu____3652 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded ctor: %s" uu____3652
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3651)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3646);
              FStar_Pervasives_Native.None))
  
let (embed_sigelt_view :
  FStar_Range.range ->
    FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun sev  ->
      match sev with
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____3674 =
            let uu____3675 =
              let uu____3676 =
                let uu____3677 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____3677  in
              let uu____3678 =
                let uu____3681 =
                  let uu____3682 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____3682  in
                let uu____3683 =
                  let uu____3686 =
                    let uu____3687 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3687  in
                  let uu____3688 =
                    let uu____3691 =
                      let uu____3692 =
                        let uu____3693 =
                          FStar_Syntax_Embeddings.embed_list embed_ctor
                            FStar_Reflection_Data.fstar_refl_ctor
                           in
                        uu____3693 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____3692  in
                    [uu____3691]  in
                  uu____3686 :: uu____3688  in
                uu____3681 :: uu____3683  in
              uu____3676 :: uu____3678  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____3675
             in
          uu____3674 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
          let uu____3706 =
            let uu____3707 =
              let uu____3708 =
                let uu____3709 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____3709  in
              let uu____3710 =
                let uu____3713 =
                  let uu____3714 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3714  in
                let uu____3715 =
                  let uu____3718 =
                    let uu____3719 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3719  in
                  [uu____3718]  in
                uu____3713 :: uu____3715  in
              uu____3708 :: uu____3710  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____3707
             in
          uu____3706 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___60_3722 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___60_3722.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___60_3722.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3733 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3733 with
    | (hd1,args) ->
        let uu____3772 =
          let uu____3785 =
            let uu____3786 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3786.FStar_Syntax_Syntax.n  in
          (uu____3785, args)  in
        (match uu____3772 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3801)::(bs,uu____3803)::(t2,uu____3805)::(dcs,uu____3807)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3862 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3862
               (fun nm1  ->
                  let uu____3874 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____3874
                    (fun bs1  ->
                       let uu____3880 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3880
                         (fun t3  ->
                            let uu____3886 =
                              let uu____3891 =
                                FStar_Syntax_Embeddings.unembed_list
                                  unembed_ctor
                                 in
                              uu____3891 dcs  in
                            FStar_Util.bind_opt uu____3886
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____3912)::(ty,uu____3914)::(t2,uu____3916)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____3961 = unembed_fvar fvar1  in
             FStar_Util.bind_opt uu____3961
               (fun fvar2  ->
                  let uu____3967 = unembed_term ty  in
                  FStar_Util.bind_opt uu____3967
                    (fun ty1  ->
                       let uu____3973 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3973
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_63  ->
                                 FStar_Pervasives_Native.Some _0_63)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____3995 ->
             ((let uu____4009 =
                 let uu____4014 =
                   let uu____4015 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____4015
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____4014)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4009);
              FStar_Pervasives_Native.None))
  
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (type_of_binder : FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.typ)
  = fun b  -> match b with | (b1,uu____4023) -> b1.FStar_Syntax_Syntax.sort 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____4030 = FStar_Syntax_Util.un_uinst t1  in
      let uu____4031 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____4030 uu____4031
  
let (fresh_binder : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.binder) =
  fun t  ->
    let uu____4035 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t  in
    (uu____4035, FStar_Pervasives_Native.None)
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 