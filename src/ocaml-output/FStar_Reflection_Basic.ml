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
      let qi = { FStar_Syntax_Syntax.qopen = false }  in
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_meta
           (FStar_Syntax_Syntax.tun,
             (FStar_Syntax_Syntax.Meta_quoted (t, qi))))
        FStar_Pervasives_Native.None rng
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____90;
           FStar_Syntax_Syntax.pos = uu____91;
           FStar_Syntax_Syntax.vars = uu____92;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> FStar_Pervasives_Native.Some qt
    | uu____105 ->
        ((let uu____107 =
            let uu____112 =
              let uu____113 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____113  in
            (FStar_Errors.Warning_NotEmbedded, uu____112)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____107);
         FStar_Pervasives_Native.None)
  
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv  ->
    let uu____121 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____121
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let uu____129 = FStar_Parser_Const.p2l ns  in
    FStar_Syntax_Syntax.lid_as_fv uu____129
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
    let uu____148 =
      let uu____149 = FStar_Syntax_Subst.compress t  in
      uu____149.FStar_Syntax_Syntax.n  in
    match uu____148 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____155 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____155
    | uu____156 ->
        ((let uu____158 =
            let uu____163 =
              let uu____164 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____164  in
            (FStar_Errors.Warning_NotEmbedded, uu____163)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____158);
         FStar_Pervasives_Native.None)
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____169 =
      let uu____170 =
        let uu____171 =
          let uu____172 =
            let uu____173 = inspect_fv fv  in
            let uu____176 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____176 i.FStar_Syntax_Syntax.rng uu____173  in
          FStar_Syntax_Syntax.as_arg uu____172  in
        [uu____171]  in
      FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv
        uu____170
       in
    uu____169 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
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
    let uu____204 =
      let uu____205 = FStar_Syntax_Subst.compress t  in
      uu____205.FStar_Syntax_Syntax.n  in
    match uu____204 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____211 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____211
    | uu____212 ->
        ((let uu____214 =
            let uu____219 =
              let uu____220 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____220  in
            (FStar_Errors.Warning_NotEmbedded, uu____219)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____214);
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
    let uu____242 =
      let uu____243 = FStar_Syntax_Subst.compress t  in
      uu____243.FStar_Syntax_Syntax.n  in
    match uu____242 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____249 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____249
    | uu____250 ->
        ((let uu____252 =
            let uu____257 =
              let uu____258 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____258  in
            (FStar_Errors.Warning_NotEmbedded, uu____257)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____252);
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
            let uu____273 =
              let uu____274 =
                let uu____275 =
                  let uu____276 =
                    let uu____277 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____277  in
                  FStar_Syntax_Syntax.as_arg uu____276  in
                [uu____275]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
                uu____274
               in
            uu____273 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____281 =
              let uu____282 =
                let uu____283 =
                  let uu____284 = FStar_Syntax_Embeddings.embed_string rng s
                     in
                  FStar_Syntax_Syntax.as_arg uu____284  in
                [uu____283]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
                uu____282
               in
            uu____281 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___55_287 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_287.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_287.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____298 = FStar_Syntax_Util.head_and_args t1  in
    match uu____298 with
    | (hd1,args) ->
        let uu____337 =
          let uu____350 =
            let uu____351 = FStar_Syntax_Util.un_uinst hd1  in
            uu____351.FStar_Syntax_Syntax.n  in
          (uu____350, args)  in
        (match uu____337 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____411)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____436 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____436
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____445)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____470 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____470
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____477 ->
             ((let uu____491 =
                 let uu____496 =
                   let uu____497 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____497
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____496)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____491);
              FStar_Pervasives_Native.None))
  
let rec (embed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedder) =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____506 =
            let uu____507 =
              let uu____508 =
                let uu____509 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____509  in
              [uu____508]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____507
             in
          uu____506 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____518 =
            let uu____519 =
              let uu____520 =
                let uu____521 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____521  in
              let uu____522 =
                let uu____525 =
                  let uu____526 =
                    let uu____527 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern
                       in
                    uu____527 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____526  in
                [uu____525]  in
              uu____520 :: uu____522  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____519
             in
          uu____518 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____538 =
            let uu____539 =
              let uu____540 =
                let uu____541 =
                  let uu____542 = FStar_Syntax_Syntax.mk_binder bv  in
                  embed_binder rng uu____542  in
                FStar_Syntax_Syntax.as_arg uu____541  in
              [uu____540]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____539
             in
          uu____538 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____546 =
            let uu____547 =
              let uu____548 =
                let uu____549 =
                  let uu____550 = FStar_Syntax_Syntax.mk_binder bv  in
                  embed_binder rng uu____550  in
                FStar_Syntax_Syntax.as_arg uu____549  in
              [uu____548]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____547
             in
          uu____546 FStar_Pervasives_Native.None rng
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____561 = FStar_Syntax_Util.head_and_args t1  in
    match uu____561 with
    | (hd1,args) ->
        let uu____600 =
          let uu____613 =
            let uu____614 = FStar_Syntax_Util.un_uinst hd1  in
            uu____614.FStar_Syntax_Syntax.n  in
          (uu____613, args)  in
        (match uu____600 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____629)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____654 = unembed_const c  in
             FStar_Util.bind_opt uu____654
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____663)::(ps,uu____665)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____700 = unembed_fvar f  in
             FStar_Util.bind_opt uu____700
               (fun f1  ->
                  let uu____706 =
                    let uu____711 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____711 ps  in
                  FStar_Util.bind_opt uu____706
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____730)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____755 = unembed_binder b  in
             FStar_Util.bind_opt uu____755
               (fun uu____761  ->
                  match uu____761 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                        (FStar_Reflection_Data.Pat_Var bv))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____770)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____795 = unembed_binder b  in
             FStar_Util.bind_opt uu____795
               (fun uu____801  ->
                  match uu____801 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                        (FStar_Reflection_Data.Pat_Wild bv))
         | uu____808 ->
             ((let uu____822 =
                 let uu____827 =
                   let uu____828 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s" uu____828
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____827)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____822);
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
      let uu___56_861 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___56_861.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___56_861.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____872 = FStar_Syntax_Util.head_and_args t1  in
    match uu____872 with
    | (hd1,args) ->
        let uu____911 =
          let uu____924 =
            let uu____925 = FStar_Syntax_Util.un_uinst hd1  in
            uu____925.FStar_Syntax_Syntax.n  in
          (uu____924, args)  in
        (match uu____911 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____968 ->
             ((let uu____982 =
                 let uu____987 =
                   let uu____988 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____988
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____987)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____982);
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
          let uu____1021 =
            let uu____1022 =
              let uu____1023 =
                let uu____1024 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1024  in
              [uu____1023]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1022
             in
          uu____1021 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1028 =
            let uu____1029 =
              let uu____1030 =
                let uu____1031 = embed_binder rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1031  in
              [uu____1030]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1029
             in
          uu____1028 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1036 =
            let uu____1037 =
              let uu____1038 =
                let uu____1039 = embed_term rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1039  in
              let uu____1040 =
                let uu____1043 =
                  let uu____1044 = embed_argv rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1044  in
                [uu____1043]  in
              uu____1038 :: uu____1040  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1037
             in
          uu____1036 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1049 =
            let uu____1050 =
              let uu____1051 =
                let uu____1052 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1052  in
              let uu____1053 =
                let uu____1056 =
                  let uu____1057 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1057  in
                [uu____1056]  in
              uu____1051 :: uu____1053  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1050
             in
          uu____1049 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1062 =
            let uu____1063 =
              let uu____1064 =
                let uu____1065 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1065  in
              let uu____1066 =
                let uu____1069 =
                  let uu____1070 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____1070  in
                [uu____1069]  in
              uu____1064 :: uu____1066  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____1063
             in
          uu____1062 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1074 =
            let uu____1075 =
              let uu____1076 =
                let uu____1077 = FStar_Syntax_Embeddings.embed_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1077  in
              [uu____1076]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____1075
             in
          uu____1074 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1082 =
            let uu____1083 =
              let uu____1084 =
                let uu____1085 = embed_binder rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1085  in
              let uu____1086 =
                let uu____1089 =
                  let uu____1090 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1090  in
                [uu____1089]  in
              uu____1084 :: uu____1086  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____1083
             in
          uu____1082 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1094 =
            let uu____1095 =
              let uu____1096 =
                let uu____1097 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1097  in
              [uu____1096]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____1095
             in
          uu____1094 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1102 =
            let uu____1103 =
              let uu____1104 =
                let uu____1105 = FStar_Syntax_Embeddings.embed_int rng u  in
                FStar_Syntax_Syntax.as_arg uu____1105  in
              let uu____1106 =
                let uu____1109 =
                  let uu____1110 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1110  in
                [uu____1109]  in
              uu____1104 :: uu____1106  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____1103
             in
          uu____1102 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1117 =
            let uu____1118 =
              let uu____1119 =
                let uu____1120 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____1120  in
              let uu____1121 =
                let uu____1124 =
                  let uu____1125 = embed_binder rng b  in
                  FStar_Syntax_Syntax.as_arg uu____1125  in
                let uu____1126 =
                  let uu____1129 =
                    let uu____1130 = embed_term rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____1130  in
                  let uu____1131 =
                    let uu____1134 =
                      let uu____1135 = embed_term rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____1135  in
                    [uu____1134]  in
                  uu____1129 :: uu____1131  in
                uu____1124 :: uu____1126  in
              uu____1119 :: uu____1121  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____1118
             in
          uu____1117 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1144 =
            let uu____1145 =
              let uu____1146 =
                let uu____1147 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____1147  in
              let uu____1148 =
                let uu____1151 =
                  let uu____1152 =
                    let uu____1153 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____1153 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____1152  in
                [uu____1151]  in
              uu____1146 :: uu____1148  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____1145
             in
          uu____1144 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___57_1171 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___57_1171.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___57_1171.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_term_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1182 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1182 with
    | (hd1,args) ->
        let uu____1221 =
          let uu____1234 =
            let uu____1235 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1235.FStar_Syntax_Syntax.n  in
          (uu____1234, args)  in
        (match uu____1221 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1250)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1275 = unembed_binder b  in
             FStar_Util.bind_opt uu____1275
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1284)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1309 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1309
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1318)::(r,uu____1320)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1355 = unembed_term l  in
             FStar_Util.bind_opt uu____1355
               (fun l1  ->
                  let uu____1361 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1361
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1386)::(t2,uu____1388)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1423 = unembed_binder b  in
             FStar_Util.bind_opt uu____1423
               (fun b1  ->
                  let uu____1429 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1429
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1438)::(t2,uu____1440)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1475 = unembed_binder b  in
             FStar_Util.bind_opt uu____1475
               (fun b1  ->
                  let uu____1481 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1481
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1490)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1515 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1515
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1524)::(t2,uu____1526)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1561 = unembed_binder b  in
             FStar_Util.bind_opt uu____1561
               (fun b1  ->
                  let uu____1567 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1567
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1576)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1601 = unembed_const c  in
             FStar_Util.bind_opt uu____1601
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1610)::(t2,uu____1612)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1647 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1647
               (fun u1  ->
                  let uu____1653 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1653
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____1662)::(b,uu____1664)::(t11,uu____1666)::(t2,uu____1668)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____1723 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____1723
               (fun r1  ->
                  let uu____1729 = unembed_binder b  in
                  FStar_Util.bind_opt uu____1729
                    (fun b1  ->
                       let uu____1735 = unembed_term t11  in
                       FStar_Util.bind_opt uu____1735
                         (fun t12  ->
                            let uu____1741 = unembed_term t2  in
                            FStar_Util.bind_opt uu____1741
                              (fun t21  ->
                                 FStar_All.pipe_left
                                   (fun _0_55  ->
                                      FStar_Pervasives_Native.Some _0_55)
                                   (FStar_Reflection_Data.Tv_Let
                                      (r1, b1, t12, t21))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1750)::(brs,uu____1752)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____1787 = unembed_term t2  in
             FStar_Util.bind_opt uu____1787
               (fun t3  ->
                  let uu____1793 =
                    let uu____1802 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____1802 brs  in
                  FStar_Util.bind_opt uu____1793
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
         | uu____1856 ->
             ((let uu____1870 =
                 let uu____1875 =
                   let uu____1876 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____1876
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1875)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1870);
              FStar_Pervasives_Native.None))
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____1887 =
            let uu____1888 =
              let uu____1889 =
                let uu____1890 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____1890  in
              [uu____1889]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____1888
             in
          uu____1887 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____1898 =
            let uu____1899 =
              let uu____1900 =
                let uu____1901 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____1901  in
              let uu____1902 =
                let uu____1905 =
                  let uu____1906 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____1906  in
                [uu____1905]  in
              uu____1900 :: uu____1902  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____1899
             in
          uu____1898 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___58_1909 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___58_1909.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___58_1909.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1920 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1920 with
    | (hd1,args) ->
        let uu____1959 =
          let uu____1972 =
            let uu____1973 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1973.FStar_Syntax_Syntax.n  in
          (uu____1972, args)  in
        (match uu____1959 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____1988)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2013 = unembed_term t2  in
             FStar_Util.bind_opt uu____2013
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2022)::(post,uu____2024)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2059 = unembed_term pre  in
             FStar_Util.bind_opt uu____2059
               (fun pre1  ->
                  let uu____2065 = unembed_term post  in
                  FStar_Util.bind_opt uu____2065
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
         | uu____2089 ->
             ((let uu____2103 =
                 let uu____2108 =
                   let uu____2109 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2109
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2108)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2103);
              FStar_Pervasives_Native.None))
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____2123::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____2148 = init xs  in x :: uu____2148
  
let (inspect_bv : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b) 
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2158) ->
        let uu____2171 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____2171
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____2173) ->
        FStar_Reflection_Data.C_String s
    | uu____2174 ->
        let uu____2175 =
          let uu____2176 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____2176  in
        failwith uu____2175
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____2183) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2189 = FStar_Syntax_Syntax.mk_binder bv  in
        FStar_Reflection_Data.Tv_Var uu____2189
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2232 = last args  in
        (match uu____2232 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____2252) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit
                in
             let uu____2253 =
               let uu____2258 =
                 let uu____2261 =
                   let uu____2262 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2262  in
                 uu____2261 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos
                  in
               (uu____2258, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____2253)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2281,uu____2282) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____2324 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____2324 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2351 =
                    let uu____2356 = FStar_Syntax_Util.abs bs2 t4 k  in
                    (b, uu____2356)  in
                  FStar_Reflection_Data.Tv_Abs uu____2351))
    | FStar_Syntax_Syntax.Tm_type uu____2361 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____2377 ->
        let uu____2390 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____2390 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____2414 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____2414 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2443 -> failwith "impossible"  in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2453 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____2453
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2480 =
          let uu____2485 =
            let uu____2486 = FStar_Syntax_Unionfind.uvar_id u  in
            FStar_BigInt.of_int_fs uu____2486  in
          (uu____2485, t3)  in
        FStar_Reflection_Data.Tv_Uvar uu____2480
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2506 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____2509 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____2509 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2538 ->
                          failwith
                            "impossible: open_term returned different amount of binders"
                       in
                    FStar_Reflection_Data.Tv_Let
                      (false, b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2566 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____2568 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____2568 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____2582 ->
                              FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              let uu____2584 =
                                let uu____2593 =
                                  FStar_Syntax_Syntax.mk_binder bv1  in
                                (true, uu____2593,
                                  (lb1.FStar_Syntax_Syntax.lbdef), t22)
                                 in
                              FStar_Reflection_Data.Tv_Let uu____2584)
                     | uu____2596 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2646 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____2646
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2665 =
                let uu____2672 =
                  FStar_List.map
                    (fun uu____2684  ->
                       match uu____2684 with
                       | (p1,uu____2692) -> inspect_pat p1) ps
                   in
                (fv, uu____2672)  in
              FStar_Reflection_Data.Pat_Cons uu____2665
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2701 ->
              failwith "NYI: Pat_dot_term"
           in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
        let brs2 =
          FStar_List.map
            (fun uu___53_2745  ->
               match uu___53_2745 with
               | (pat,uu____2767,t4) ->
                   let uu____2785 = inspect_pat pat  in (uu____2785, t4))
            brs1
           in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2798 ->
        ((let uu____2800 =
            let uu____2805 =
              let uu____2806 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____2807 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____2806
                uu____2807
               in
            (FStar_Errors.Warning_CantInspect, uu____2805)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____2800);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2812) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2823)::(post,uu____2825)::uu____2826 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2859 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2869 ->
        FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2882 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2887 =
          let uu____2898 = FStar_BigInt.string_of_big_int i  in
          (uu____2898, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____2887
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2914) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2923 =
               let uu____2932 = FStar_Syntax_Syntax.as_arg r  in [uu____2932]
                in
             FStar_Syntax_Util.mk_app l uu____2923
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2933 =
               let uu____2942 = FStar_Syntax_Syntax.iarg r  in [uu____2942]
                in
             FStar_Syntax_Util.mk_app l uu____2933)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2948),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2955 =
          let uu____2958 =
            let uu____2959 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____2959  in
          FStar_Syntax_Syntax.mk uu____2958  in
        uu____2955 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____2965 = FStar_BigInt.to_int_fs u  in
        FStar_Syntax_Util.uvar_from_id uu____2965 t
    | FStar_Reflection_Data.Tv_Let (false ,b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b  in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____2973 =
          let uu____2976 =
            let uu____2977 =
              let uu____2990 = FStar_Syntax_Subst.close [b] t2  in
              ((false, [lb]), uu____2990)  in
            FStar_Syntax_Syntax.Tm_let uu____2977  in
          FStar_Syntax_Syntax.mk uu____2976  in
        uu____2973 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (true ,b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b  in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____3009 = FStar_Syntax_Subst.open_let_rec [lb] t2  in
        (match uu____3009 with
         | (lbs_open,body_open) ->
             let uu____3022 = FStar_Syntax_Subst.close_let_rec [lb] body_open
                in
             (match uu____3022 with
              | (lbs,body) ->
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange))
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____3060 =
                let uu____3061 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____3061  in
              FStar_All.pipe_left wrap uu____3060
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____3070 =
                let uu____3071 =
                  let uu____3084 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____3098 = pack_pat p1  in (uu____3098, false))
                      ps
                     in
                  (fv, uu____3084)  in
                FStar_Syntax_Syntax.Pat_cons uu____3071  in
              FStar_All.pipe_left wrap uu____3070
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
           in
        let brs1 =
          FStar_List.map
            (fun uu___54_3144  ->
               match uu___54_3144 with
               | (pat,t1) ->
                   let uu____3161 = pack_pat pat  in
                   (uu____3161, FStar_Pervasives_Native.None, t1)) brs
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
      let uu___59_3183 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___59_3183.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___59_3183.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3194 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3194 with
    | (hd1,args) ->
        let uu____3233 =
          let uu____3246 =
            let uu____3247 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3247.FStar_Syntax_Syntax.n  in
          (uu____3246, args)  in
        (match uu____3233 with
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
         | uu____3305 ->
             ((let uu____3319 =
                 let uu____3324 =
                   let uu____3325 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____3325
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3324)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3319);
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____3371,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____3472,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1  in
               let ctor1 dc_lid =
                 let uu____3489 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid  in
                 match uu____3489 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3542,n1,uu____3544) ->
                          let uu____3549 =
                            let uu____3554 = FStar_Ident.path_of_lid lid2  in
                            (uu____3554, t1)  in
                          FStar_Reflection_Data.Ctor uu____3549
                      | uu____3559 -> failwith "wat 1")
                 | uu____3560 -> failwith "wat 2"  in
               let ctors = FStar_List.map ctor1 dc_lids  in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3569) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____3584 ->
                     failwith "global Sig_let has bv"
                  in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____3589 -> FStar_Reflection_Data.Unk)
  
let (embed_ctor :
  FStar_Range.range -> FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      match c with
      | FStar_Reflection_Data.Ctor (nm,t) ->
          let uu____3601 =
            let uu____3602 =
              let uu____3603 =
                let uu____3604 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____3604  in
              let uu____3605 =
                let uu____3608 =
                  let uu____3609 = embed_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____3609  in
                [uu____3608]  in
              uu____3603 :: uu____3605  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Ctor.FStar_Reflection_Data.t
              uu____3602
             in
          uu____3601 FStar_Pervasives_Native.None rng
  
let (unembed_ctor :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.ctor FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3622 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3622 with
    | (hd1,args) ->
        let uu____3661 =
          let uu____3674 =
            let uu____3675 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3675.FStar_Syntax_Syntax.n  in
          (uu____3674, args)  in
        (match uu____3661 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3690)::(t2,uu____3692)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor.FStar_Reflection_Data.lid
             ->
             let uu____3727 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3727
               (fun nm1  ->
                  let uu____3739 = unembed_term t2  in
                  FStar_Util.bind_opt uu____3739
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.Ctor (nm1, t3))))
         | uu____3748 ->
             ((let uu____3762 =
                 let uu____3767 =
                   let uu____3768 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded ctor: %s" uu____3768
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3767)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3762);
              FStar_Pervasives_Native.None))
  
let (embed_sigelt_view :
  FStar_Range.range ->
    FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun sev  ->
      match sev with
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____3790 =
            let uu____3791 =
              let uu____3792 =
                let uu____3793 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____3793  in
              let uu____3794 =
                let uu____3797 =
                  let uu____3798 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____3798  in
                let uu____3799 =
                  let uu____3802 =
                    let uu____3803 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3803  in
                  let uu____3804 =
                    let uu____3807 =
                      let uu____3808 =
                        let uu____3809 =
                          FStar_Syntax_Embeddings.embed_list embed_ctor
                            FStar_Reflection_Data.fstar_refl_ctor
                           in
                        uu____3809 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____3808  in
                    [uu____3807]  in
                  uu____3802 :: uu____3804  in
                uu____3797 :: uu____3799  in
              uu____3792 :: uu____3794  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____3791
             in
          uu____3790 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
          let uu____3822 =
            let uu____3823 =
              let uu____3824 =
                let uu____3825 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____3825  in
              let uu____3826 =
                let uu____3829 =
                  let uu____3830 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3830  in
                let uu____3831 =
                  let uu____3834 =
                    let uu____3835 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3835  in
                  [uu____3834]  in
                uu____3829 :: uu____3831  in
              uu____3824 :: uu____3826  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____3823
             in
          uu____3822 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___60_3838 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___60_3838.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___60_3838.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3849 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3849 with
    | (hd1,args) ->
        let uu____3888 =
          let uu____3901 =
            let uu____3902 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3902.FStar_Syntax_Syntax.n  in
          (uu____3901, args)  in
        (match uu____3888 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3917)::(bs,uu____3919)::(t2,uu____3921)::(dcs,uu____3923)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3978 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3978
               (fun nm1  ->
                  let uu____3990 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____3990
                    (fun bs1  ->
                       let uu____3996 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3996
                         (fun t3  ->
                            let uu____4002 =
                              let uu____4007 =
                                FStar_Syntax_Embeddings.unembed_list
                                  unembed_ctor
                                 in
                              uu____4007 dcs  in
                            FStar_Util.bind_opt uu____4002
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____4028)::(ty,uu____4030)::(t2,uu____4032)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____4077 = unembed_fvar fvar1  in
             FStar_Util.bind_opt uu____4077
               (fun fvar2  ->
                  let uu____4083 = unembed_term ty  in
                  FStar_Util.bind_opt uu____4083
                    (fun ty1  ->
                       let uu____4089 = unembed_term t2  in
                       FStar_Util.bind_opt uu____4089
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_63  ->
                                 FStar_Pervasives_Native.Some _0_63)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____4111 ->
             ((let uu____4125 =
                 let uu____4130 =
                   let uu____4131 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____4131
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____4130)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4125);
              FStar_Pervasives_Native.None))
  
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (type_of_binder : FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.typ)
  = fun b  -> match b with | (b1,uu____4139) -> b1.FStar_Syntax_Syntax.sort 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____4146 = FStar_Syntax_Util.un_uinst t1  in
      let uu____4147 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____4146 uu____4147
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 