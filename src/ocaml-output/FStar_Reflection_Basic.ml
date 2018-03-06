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
      | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
          let uu____1116 =
            let uu____1117 =
              let uu____1118 =
                let uu____1119 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1119  in
              let uu____1120 =
                let uu____1123 =
                  let uu____1124 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1124  in
                let uu____1125 =
                  let uu____1128 =
                    let uu____1129 = embed_term rng t2  in
                    FStar_Syntax_Syntax.as_arg uu____1129  in
                  [uu____1128]  in
                uu____1123 :: uu____1125  in
              uu____1118 :: uu____1120  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____1117
             in
          uu____1116 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1138 =
            let uu____1139 =
              let uu____1140 =
                let uu____1141 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____1141  in
              let uu____1142 =
                let uu____1145 =
                  let uu____1146 =
                    let uu____1147 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____1147 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____1146  in
                [uu____1145]  in
              uu____1140 :: uu____1142  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____1139
             in
          uu____1138 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___57_1165 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___57_1165.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___57_1165.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_term_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1176 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1176 with
    | (hd1,args) ->
        let uu____1215 =
          let uu____1228 =
            let uu____1229 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1229.FStar_Syntax_Syntax.n  in
          (uu____1228, args)  in
        (match uu____1215 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1244)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1269 = unembed_binder b  in
             FStar_Util.bind_opt uu____1269
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1278)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1303 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1303
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1312)::(r,uu____1314)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1349 = unembed_term l  in
             FStar_Util.bind_opt uu____1349
               (fun l1  ->
                  let uu____1355 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1355
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1380)::(t2,uu____1382)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1417 = unembed_binder b  in
             FStar_Util.bind_opt uu____1417
               (fun b1  ->
                  let uu____1423 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1423
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1432)::(t2,uu____1434)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1469 = unembed_binder b  in
             FStar_Util.bind_opt uu____1469
               (fun b1  ->
                  let uu____1475 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1475
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1484)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1509 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1509
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1518)::(t2,uu____1520)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1555 = unembed_binder b  in
             FStar_Util.bind_opt uu____1555
               (fun b1  ->
                  let uu____1561 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1561
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1570)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1595 = unembed_const c  in
             FStar_Util.bind_opt uu____1595
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1604)::(t2,uu____1606)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1641 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1641
               (fun u1  ->
                  let uu____1647 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1647
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1656)::(t11,uu____1658)::(t2,uu____1660)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____1705 = unembed_binder b  in
             FStar_Util.bind_opt uu____1705
               (fun b1  ->
                  let uu____1711 = unembed_term t11  in
                  FStar_Util.bind_opt uu____1711
                    (fun t12  ->
                       let uu____1717 = unembed_term t2  in
                       FStar_Util.bind_opt uu____1717
                         (fun t21  ->
                            FStar_All.pipe_left
                              (fun _0_55  ->
                                 FStar_Pervasives_Native.Some _0_55)
                              (FStar_Reflection_Data.Tv_Let (b1, t12, t21)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1726)::(brs,uu____1728)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____1763 = unembed_term t2  in
             FStar_Util.bind_opt uu____1763
               (fun t3  ->
                  let uu____1769 =
                    let uu____1778 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____1778 brs  in
                  FStar_Util.bind_opt uu____1769
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
         | uu____1832 ->
             ((let uu____1846 =
                 let uu____1851 =
                   let uu____1852 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____1852
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1851)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1846);
              FStar_Pervasives_Native.None))
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____1863 =
            let uu____1864 =
              let uu____1865 =
                let uu____1866 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____1866  in
              [uu____1865]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____1864
             in
          uu____1863 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____1874 =
            let uu____1875 =
              let uu____1876 =
                let uu____1877 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____1877  in
              let uu____1878 =
                let uu____1881 =
                  let uu____1882 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____1882  in
                [uu____1881]  in
              uu____1876 :: uu____1878  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____1875
             in
          uu____1874 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___58_1885 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___58_1885.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___58_1885.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1896 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1896 with
    | (hd1,args) ->
        let uu____1935 =
          let uu____1948 =
            let uu____1949 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1949.FStar_Syntax_Syntax.n  in
          (uu____1948, args)  in
        (match uu____1935 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____1964)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____1989 = unembed_term t2  in
             FStar_Util.bind_opt uu____1989
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____1998)::(post,uu____2000)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2035 = unembed_term pre  in
             FStar_Util.bind_opt uu____2035
               (fun pre1  ->
                  let uu____2041 = unembed_term post  in
                  FStar_Util.bind_opt uu____2041
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
         | uu____2065 ->
             ((let uu____2079 =
                 let uu____2084 =
                   let uu____2085 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2085
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2084)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2079);
              FStar_Pervasives_Native.None))
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____2099::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____2124 = init xs  in x :: uu____2124
  
let (inspect_bv : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b) 
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2134) ->
        let uu____2147 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____2147
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____2149) ->
        FStar_Reflection_Data.C_String s
    | uu____2150 ->
        let uu____2151 =
          let uu____2152 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____2152  in
        failwith uu____2151
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____2159) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2165 = FStar_Syntax_Syntax.mk_binder bv  in
        FStar_Reflection_Data.Tv_Var uu____2165
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2208 = last args  in
        (match uu____2208 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____2228) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit
                in
             let uu____2229 =
               let uu____2234 =
                 let uu____2237 =
                   let uu____2238 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2238  in
                 uu____2237 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos
                  in
               (uu____2234, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____2229)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2257,uu____2258) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____2300 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____2300 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2327 =
                    let uu____2332 = FStar_Syntax_Util.abs bs2 t4 k  in
                    (b, uu____2332)  in
                  FStar_Reflection_Data.Tv_Abs uu____2327))
    | FStar_Syntax_Syntax.Tm_type uu____2337 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____2353 ->
        let uu____2366 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____2366 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____2390 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____2390 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2419 -> failwith "impossible"  in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2429 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____2429
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2456 =
          let uu____2461 =
            let uu____2462 = FStar_Syntax_Unionfind.uvar_id u  in
            FStar_BigInt.of_int_fs uu____2462  in
          (uu____2461, t3)  in
        FStar_Reflection_Data.Tv_Uvar uu____2456
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2482 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____2485 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____2485 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2514 ->
                          failwith
                            "impossible: open_term returned different amount of binders"
                       in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2572 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____2572
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2591 =
                let uu____2598 =
                  FStar_List.map
                    (fun uu____2610  ->
                       match uu____2610 with
                       | (p1,uu____2618) -> inspect_pat p1) ps
                   in
                (fv, uu____2598)  in
              FStar_Reflection_Data.Pat_Cons uu____2591
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2627 ->
              failwith "NYI: Pat_dot_term"
           in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
        let brs2 =
          FStar_List.map
            (fun uu___53_2671  ->
               match uu___53_2671 with
               | (pat,uu____2693,t4) ->
                   let uu____2711 = inspect_pat pat  in (uu____2711, t4))
            brs1
           in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2724 ->
        ((let uu____2726 =
            let uu____2731 =
              let uu____2732 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____2733 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____2732
                uu____2733
               in
            (FStar_Errors.Warning_CantInspect, uu____2731)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____2726);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2738) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2749)::(post,uu____2751)::uu____2752 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2785 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2795 ->
        FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2808 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2813 =
          let uu____2824 = FStar_BigInt.string_of_big_int i  in
          (uu____2824, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____2813
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2840) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2849 =
               let uu____2858 = FStar_Syntax_Syntax.as_arg r  in [uu____2858]
                in
             FStar_Syntax_Util.mk_app l uu____2849
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2859 =
               let uu____2868 = FStar_Syntax_Syntax.iarg r  in [uu____2868]
                in
             FStar_Syntax_Util.mk_app l uu____2859)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2874),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2881 =
          let uu____2884 =
            let uu____2885 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____2885  in
          FStar_Syntax_Syntax.mk uu____2884  in
        uu____2881 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____2891 = FStar_BigInt.to_int_fs u  in
        FStar_Syntax_Util.uvar_from_id uu____2891 t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b  in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            []
           in
        let uu____2899 =
          let uu____2902 =
            let uu____2903 =
              let uu____2916 = FStar_Syntax_Subst.close [b] t2  in
              ((false, [lb]), uu____2916)  in
            FStar_Syntax_Syntax.Tm_let uu____2903  in
          FStar_Syntax_Syntax.mk uu____2902  in
        uu____2899 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2945 =
                let uu____2946 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____2946  in
              FStar_All.pipe_left wrap uu____2945
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2955 =
                let uu____2956 =
                  let uu____2969 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2983 = pack_pat p1  in (uu____2983, false))
                      ps
                     in
                  (fv, uu____2969)  in
                FStar_Syntax_Syntax.Pat_cons uu____2956  in
              FStar_All.pipe_left wrap uu____2955
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
           in
        let brs1 =
          FStar_List.map
            (fun uu___54_3029  ->
               match uu___54_3029 with
               | (pat,t1) ->
                   let uu____3046 = pack_pat pat  in
                   (uu____3046, FStar_Pervasives_Native.None, t1)) brs
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
      let uu___59_3068 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___59_3068.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___59_3068.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3079 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3079 with
    | (hd1,args) ->
        let uu____3118 =
          let uu____3131 =
            let uu____3132 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3132.FStar_Syntax_Syntax.n  in
          (uu____3131, args)  in
        (match uu____3118 with
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
         | uu____3190 ->
             ((let uu____3204 =
                 let uu____3209 =
                   let uu____3210 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____3210
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3209)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3204);
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____3256,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____3357,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1  in
               let ctor1 dc_lid =
                 let uu____3374 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid  in
                 match uu____3374 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3427,n1,uu____3429) ->
                          let uu____3434 =
                            let uu____3439 = FStar_Ident.path_of_lid lid2  in
                            (uu____3439, t1)  in
                          FStar_Reflection_Data.Ctor uu____3434
                      | uu____3444 -> failwith "wat 1")
                 | uu____3445 -> failwith "wat 2"  in
               let ctors = FStar_List.map ctor1 dc_lids  in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3454) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____3469 ->
                     failwith "global Sig_let has bv"
                  in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____3474 -> FStar_Reflection_Data.Unk)
  
let (embed_ctor :
  FStar_Range.range -> FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      match c with
      | FStar_Reflection_Data.Ctor (nm,t) ->
          let uu____3486 =
            let uu____3487 =
              let uu____3488 =
                let uu____3489 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____3489  in
              let uu____3490 =
                let uu____3493 =
                  let uu____3494 = embed_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____3494  in
                [uu____3493]  in
              uu____3488 :: uu____3490  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Ctor.FStar_Reflection_Data.t
              uu____3487
             in
          uu____3486 FStar_Pervasives_Native.None rng
  
let (unembed_ctor :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.ctor FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3507 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3507 with
    | (hd1,args) ->
        let uu____3546 =
          let uu____3559 =
            let uu____3560 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3560.FStar_Syntax_Syntax.n  in
          (uu____3559, args)  in
        (match uu____3546 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3575)::(t2,uu____3577)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor.FStar_Reflection_Data.lid
             ->
             let uu____3612 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3612
               (fun nm1  ->
                  let uu____3624 = unembed_term t2  in
                  FStar_Util.bind_opt uu____3624
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.Ctor (nm1, t3))))
         | uu____3633 ->
             ((let uu____3647 =
                 let uu____3652 =
                   let uu____3653 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded ctor: %s" uu____3653
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3652)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3647);
              FStar_Pervasives_Native.None))
  
let (embed_sigelt_view :
  FStar_Range.range ->
    FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun sev  ->
      match sev with
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____3675 =
            let uu____3676 =
              let uu____3677 =
                let uu____3678 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____3678  in
              let uu____3679 =
                let uu____3682 =
                  let uu____3683 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____3683  in
                let uu____3684 =
                  let uu____3687 =
                    let uu____3688 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3688  in
                  let uu____3689 =
                    let uu____3692 =
                      let uu____3693 =
                        let uu____3694 =
                          FStar_Syntax_Embeddings.embed_list embed_ctor
                            FStar_Reflection_Data.fstar_refl_ctor
                           in
                        uu____3694 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____3693  in
                    [uu____3692]  in
                  uu____3687 :: uu____3689  in
                uu____3682 :: uu____3684  in
              uu____3677 :: uu____3679  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____3676
             in
          uu____3675 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
          let uu____3707 =
            let uu____3708 =
              let uu____3709 =
                let uu____3710 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____3710  in
              let uu____3711 =
                let uu____3714 =
                  let uu____3715 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3715  in
                let uu____3716 =
                  let uu____3719 =
                    let uu____3720 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3720  in
                  [uu____3719]  in
                uu____3714 :: uu____3716  in
              uu____3709 :: uu____3711  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____3708
             in
          uu____3707 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___60_3723 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___60_3723.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___60_3723.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3734 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3734 with
    | (hd1,args) ->
        let uu____3773 =
          let uu____3786 =
            let uu____3787 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3787.FStar_Syntax_Syntax.n  in
          (uu____3786, args)  in
        (match uu____3773 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3802)::(bs,uu____3804)::(t2,uu____3806)::(dcs,uu____3808)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3863 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3863
               (fun nm1  ->
                  let uu____3875 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____3875
                    (fun bs1  ->
                       let uu____3881 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3881
                         (fun t3  ->
                            let uu____3887 =
                              let uu____3892 =
                                FStar_Syntax_Embeddings.unembed_list
                                  unembed_ctor
                                 in
                              uu____3892 dcs  in
                            FStar_Util.bind_opt uu____3887
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____3913)::(ty,uu____3915)::(t2,uu____3917)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____3962 = unembed_fvar fvar1  in
             FStar_Util.bind_opt uu____3962
               (fun fvar2  ->
                  let uu____3968 = unembed_term ty  in
                  FStar_Util.bind_opt uu____3968
                    (fun ty1  ->
                       let uu____3974 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3974
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_63  ->
                                 FStar_Pervasives_Native.Some _0_63)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____3996 ->
             ((let uu____4010 =
                 let uu____4015 =
                   let uu____4016 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____4016
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____4015)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4010);
              FStar_Pervasives_Native.None))
  
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (type_of_binder : FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.typ)
  = fun b  -> match b with | (b1,uu____4024) -> b1.FStar_Syntax_Syntax.sort 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____4031 = FStar_Syntax_Util.un_uinst t1  in
      let uu____4032 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____4031 uu____4032
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 