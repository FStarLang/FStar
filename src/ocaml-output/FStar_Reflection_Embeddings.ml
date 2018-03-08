open Prims
let (embed_binder :
  FStar_Range.range -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun b  ->
      FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_binder
        FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some rng)
  
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
      let uu___51_30 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___51_30.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___51_30.FStar_Syntax_Syntax.vars)
      }
  
let (embed_binders :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun l  ->
      let uu____40 =
        FStar_Syntax_Embeddings.embed_list embed_binder
          FStar_Reflection_Data.fstar_refl_binder
         in
      uu____40 rng l
  
let (embed_fvar :
  FStar_Range.range -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun fv  ->
      FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
        FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng)
  
let (embed_comp :
  FStar_Range.range -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
        FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng)
  
let (embed_env :
  FStar_Range.range -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun e  ->
      FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
        FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng)
  
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
            let uu____86 =
              let uu____87 =
                let uu____88 =
                  let uu____89 =
                    let uu____90 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____90  in
                  FStar_Syntax_Syntax.as_arg uu____89  in
                [uu____88]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
                uu____87
               in
            uu____86 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____94 =
              let uu____95 =
                let uu____96 =
                  let uu____97 = FStar_Syntax_Embeddings.embed_string rng s
                     in
                  FStar_Syntax_Syntax.as_arg uu____97  in
                [uu____96]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
                uu____95
               in
            uu____94 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___52_100 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___52_100.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___52_100.FStar_Syntax_Syntax.vars)
      }
  
let rec (embed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedder) =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____109 =
            let uu____110 =
              let uu____111 =
                let uu____112 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____112  in
              [uu____111]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____110
             in
          uu____109 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____121 =
            let uu____122 =
              let uu____123 =
                let uu____124 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____124  in
              let uu____125 =
                let uu____128 =
                  let uu____129 =
                    let uu____130 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern
                       in
                    uu____130 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____129  in
                [uu____128]  in
              uu____123 :: uu____125  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____122
             in
          uu____121 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var b ->
          let uu____141 =
            let uu____142 =
              let uu____143 =
                let uu____144 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____144  in
              [uu____143]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____142
             in
          uu____141 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild b ->
          let uu____148 =
            let uu____149 =
              let uu____150 =
                let uu____151 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____151  in
              [uu____150]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____149
             in
          uu____148 FStar_Pervasives_Native.None rng
  
let (embed_branch :
  FStar_Range.range ->
    FStar_Reflection_Data.branch -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun br  ->
      let uu____163 =
        FStar_Syntax_Embeddings.embed_pair embed_pattern
          FStar_Reflection_Data.fstar_refl_pattern embed_term
          FStar_Syntax_Syntax.t_term
         in
      uu____163 rng br
  
let (embed_argv :
  FStar_Range.range -> FStar_Reflection_Data.argv -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun aq  ->
      let uu____182 =
        FStar_Syntax_Embeddings.embed_pair embed_term
          FStar_Syntax_Syntax.t_term embed_aqualv
          FStar_Reflection_Data.fstar_refl_aqualv
         in
      uu____182 rng aq
  
let (embed_term_view :
  FStar_Range.range ->
    FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  ->
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____202 =
            let uu____203 =
              let uu____204 =
                let uu____205 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____205  in
              [uu____204]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____203
             in
          uu____202 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____209 =
            let uu____210 =
              let uu____211 =
                let uu____212 = embed_binder rng bv  in
                FStar_Syntax_Syntax.as_arg uu____212  in
              [uu____211]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____210
             in
          uu____209 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____217 =
            let uu____218 =
              let uu____219 =
                let uu____220 = embed_term rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____220  in
              let uu____221 =
                let uu____224 =
                  let uu____225 = embed_argv rng a  in
                  FStar_Syntax_Syntax.as_arg uu____225  in
                [uu____224]  in
              uu____219 :: uu____221  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____218
             in
          uu____217 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____230 =
            let uu____231 =
              let uu____232 =
                let uu____233 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____233  in
              let uu____234 =
                let uu____237 =
                  let uu____238 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____238  in
                [uu____237]  in
              uu____232 :: uu____234  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____231
             in
          uu____230 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____243 =
            let uu____244 =
              let uu____245 =
                let uu____246 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____246  in
              let uu____247 =
                let uu____250 =
                  let uu____251 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____251  in
                [uu____250]  in
              uu____245 :: uu____247  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____244
             in
          uu____243 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____255 =
            let uu____256 =
              let uu____257 =
                let uu____258 = FStar_Syntax_Embeddings.embed_unit rng ()  in
                FStar_Syntax_Syntax.as_arg uu____258  in
              [uu____257]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____256
             in
          uu____255 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____263 =
            let uu____264 =
              let uu____265 =
                let uu____266 = embed_binder rng bv  in
                FStar_Syntax_Syntax.as_arg uu____266  in
              let uu____267 =
                let uu____270 =
                  let uu____271 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____271  in
                [uu____270]  in
              uu____265 :: uu____267  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____264
             in
          uu____263 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____275 =
            let uu____276 =
              let uu____277 =
                let uu____278 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____278  in
              [uu____277]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____276
             in
          uu____275 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____283 =
            let uu____284 =
              let uu____285 =
                let uu____286 = FStar_Syntax_Embeddings.embed_int rng u  in
                FStar_Syntax_Syntax.as_arg uu____286  in
              let uu____287 =
                let uu____290 =
                  let uu____291 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____291  in
                [uu____290]  in
              uu____285 :: uu____287  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____284
             in
          uu____283 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
          let uu____297 =
            let uu____298 =
              let uu____299 =
                let uu____300 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____300  in
              let uu____301 =
                let uu____304 =
                  let uu____305 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____305  in
                let uu____306 =
                  let uu____309 =
                    let uu____310 = embed_term rng t2  in
                    FStar_Syntax_Syntax.as_arg uu____310  in
                  [uu____309]  in
                uu____304 :: uu____306  in
              uu____299 :: uu____301  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____298
             in
          uu____297 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____319 =
            let uu____320 =
              let uu____321 =
                let uu____322 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____322  in
              let uu____323 =
                let uu____326 =
                  let uu____327 =
                    let uu____328 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____328 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____327  in
                [uu____326]  in
              uu____321 :: uu____323  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____320
             in
          uu____319 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___53_338 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___53_338.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___53_338.FStar_Syntax_Syntax.vars)
          }
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____349 =
            let uu____350 =
              let uu____351 =
                let uu____352 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____352  in
              [uu____351]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____350
             in
          uu____349 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____360 =
            let uu____361 =
              let uu____362 =
                let uu____363 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____363  in
              let uu____364 =
                let uu____367 =
                  let uu____368 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____368  in
                [uu____367]  in
              uu____362 :: uu____364  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____361
             in
          uu____360 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___54_371 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___54_371.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___54_371.FStar_Syntax_Syntax.vars)
          }
  
let (embed_order :
  FStar_Range.range -> FStar_Order.order -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun o  ->
      let r =
        match o with
        | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
        | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
        | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt  in
      let uu___55_382 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_382.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_382.FStar_Syntax_Syntax.vars)
      }
  
let (embed_ctor :
  FStar_Range.range -> FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      match c with
      | FStar_Reflection_Data.Ctor (nm,t) ->
          let uu____394 =
            let uu____395 =
              let uu____396 =
                let uu____397 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____397  in
              let uu____398 =
                let uu____401 =
                  let uu____402 = embed_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____402  in
                [uu____401]  in
              uu____396 :: uu____398  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Ctor.FStar_Reflection_Data.t
              uu____395
             in
          uu____394 FStar_Pervasives_Native.None rng
  
let (embed_sigelt_view :
  FStar_Range.range ->
    FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun sev  ->
      match sev with
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____426 =
            let uu____427 =
              let uu____428 =
                let uu____429 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____429  in
              let uu____430 =
                let uu____433 =
                  let uu____434 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____434  in
                let uu____435 =
                  let uu____438 =
                    let uu____439 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____439  in
                  let uu____440 =
                    let uu____443 =
                      let uu____444 =
                        let uu____445 =
                          FStar_Syntax_Embeddings.embed_list embed_ctor
                            FStar_Reflection_Data.fstar_refl_ctor
                           in
                        uu____445 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____444  in
                    [uu____443]  in
                  uu____438 :: uu____440  in
                uu____433 :: uu____435  in
              uu____428 :: uu____430  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____427
             in
          uu____426 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
          let uu____458 =
            let uu____459 =
              let uu____460 =
                let uu____461 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____461  in
              let uu____462 =
                let uu____465 =
                  let uu____466 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____466  in
                let uu____467 =
                  let uu____470 =
                    let uu____471 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____471  in
                  [uu____470]  in
                uu____465 :: uu____467  in
              uu____460 :: uu____462  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____459
             in
          uu____458 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___56_474 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___56_474.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___56_474.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____484 =
      let uu____485 = FStar_Syntax_Subst.compress t  in
      uu____485.FStar_Syntax_Syntax.n  in
    match uu____484 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____491 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____491
    | uu____492 ->
        ((let uu____494 =
            let uu____499 =
              let uu____500 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____500  in
            (FStar_Errors.Warning_NotEmbedded, uu____499)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____494);
         FStar_Pervasives_Native.None)
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____511;
           FStar_Syntax_Syntax.pos = uu____512;
           FStar_Syntax_Syntax.vars = uu____513;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> FStar_Pervasives_Native.Some qt
    | uu____526 ->
        ((let uu____528 =
            let uu____533 =
              let uu____534 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____534  in
            (FStar_Errors.Warning_NotEmbedded, uu____533)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____528);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____545 = FStar_Syntax_Util.head_and_args t1  in
    match uu____545 with
    | (hd1,args) ->
        let uu____584 =
          let uu____597 =
            let uu____598 = FStar_Syntax_Util.un_uinst hd1  in
            uu____598.FStar_Syntax_Syntax.n  in
          (uu____597, args)  in
        (match uu____584 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____641 ->
             ((let uu____655 =
                 let uu____660 =
                   let uu____661 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____661
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____660)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____655);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____669 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____669 t
  
let (unembed_fvar :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____685 =
      let uu____686 = FStar_Syntax_Subst.compress t  in
      uu____686.FStar_Syntax_Syntax.n  in
    match uu____685 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____692 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____692
    | uu____693 ->
        ((let uu____695 =
            let uu____700 =
              let uu____701 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____701  in
            (FStar_Errors.Warning_NotEmbedded, uu____700)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____695);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____711 =
      let uu____712 = FStar_Syntax_Subst.compress t  in
      uu____712.FStar_Syntax_Syntax.n  in
    match uu____711 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____718 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____718
    | uu____719 ->
        ((let uu____721 =
            let uu____726 =
              let uu____727 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____727  in
            (FStar_Errors.Warning_NotEmbedded, uu____726)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____721);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____737 =
      let uu____738 = FStar_Syntax_Subst.compress t  in
      uu____738.FStar_Syntax_Syntax.n  in
    match uu____737 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____744 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____744
    | uu____745 ->
        ((let uu____747 =
            let uu____752 =
              let uu____753 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____753  in
            (FStar_Errors.Warning_NotEmbedded, uu____752)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____747);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____764 = FStar_Syntax_Util.head_and_args t1  in
    match uu____764 with
    | (hd1,args) ->
        let uu____803 =
          let uu____816 =
            let uu____817 = FStar_Syntax_Util.un_uinst hd1  in
            uu____817.FStar_Syntax_Syntax.n  in
          (uu____816, args)  in
        (match uu____803 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____877)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____902 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____902
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____911)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____936 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____936
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____943 ->
             ((let uu____957 =
                 let uu____962 =
                   let uu____963 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____963
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____962)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____957);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____972 = FStar_Syntax_Util.head_and_args t1  in
    match uu____972 with
    | (hd1,args) ->
        let uu____1011 =
          let uu____1024 =
            let uu____1025 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1025.FStar_Syntax_Syntax.n  in
          (uu____1024, args)  in
        (match uu____1011 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1040)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1065 = unembed_const c  in
             FStar_Util.bind_opt uu____1065
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1074)::(ps,uu____1076)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1111 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1111
               (fun f1  ->
                  let uu____1117 =
                    let uu____1122 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1122 ps  in
                  FStar_Util.bind_opt uu____1117
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1141)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1166 = unembed_binder b  in
             FStar_Util.bind_opt uu____1166
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1175)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1200 = unembed_binder b  in
             FStar_Util.bind_opt uu____1200
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild b1))
         | uu____1207 ->
             ((let uu____1221 =
                 let uu____1226 =
                   let uu____1227 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1227
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1226)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1221);
              FStar_Pervasives_Native.None))
  
let (unembed_branch :
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_pair unembed_pattern unembed_term 
let (unembed_argv :
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_pair unembed_term unembed_aqualv 
let (unembed_term_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1258 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1258 with
    | (hd1,args) ->
        let uu____1297 =
          let uu____1310 =
            let uu____1311 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1311.FStar_Syntax_Syntax.n  in
          (uu____1310, args)  in
        (match uu____1297 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1326)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1351 = unembed_binder b  in
             FStar_Util.bind_opt uu____1351
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1360)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1385 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1385
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1394)::(r,uu____1396)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1431 = unembed_term l  in
             FStar_Util.bind_opt uu____1431
               (fun l1  ->
                  let uu____1437 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1437
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1462)::(t2,uu____1464)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1499 = unembed_binder b  in
             FStar_Util.bind_opt uu____1499
               (fun b1  ->
                  let uu____1505 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1505
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1514)::(t2,uu____1516)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1551 = unembed_binder b  in
             FStar_Util.bind_opt uu____1551
               (fun b1  ->
                  let uu____1557 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1557
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1566)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1591 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1591
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1600)::(t2,uu____1602)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1637 = unembed_binder b  in
             FStar_Util.bind_opt uu____1637
               (fun b1  ->
                  let uu____1643 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1643
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1652)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1677 = unembed_const c  in
             FStar_Util.bind_opt uu____1677
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1686)::(t2,uu____1688)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1723 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1723
               (fun u1  ->
                  let uu____1729 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1729
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1738)::(t11,uu____1740)::(t2,uu____1742)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____1787 = unembed_binder b  in
             FStar_Util.bind_opt uu____1787
               (fun b1  ->
                  let uu____1793 = unembed_term t11  in
                  FStar_Util.bind_opt uu____1793
                    (fun t12  ->
                       let uu____1799 = unembed_term t2  in
                       FStar_Util.bind_opt uu____1799
                         (fun t21  ->
                            FStar_All.pipe_left
                              (fun _0_55  ->
                                 FStar_Pervasives_Native.Some _0_55)
                              (FStar_Reflection_Data.Tv_Let (b1, t12, t21)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1808)::(brs,uu____1810)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____1845 = unembed_term t2  in
             FStar_Util.bind_opt uu____1845
               (fun t3  ->
                  let uu____1851 =
                    let uu____1860 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____1860 brs  in
                  FStar_Util.bind_opt uu____1851
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
         | uu____1914 ->
             ((let uu____1928 =
                 let uu____1933 =
                   let uu____1934 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____1934
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1933)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1928);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1945 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1945 with
    | (hd1,args) ->
        let uu____1984 =
          let uu____1997 =
            let uu____1998 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1998.FStar_Syntax_Syntax.n  in
          (uu____1997, args)  in
        (match uu____1984 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____2013)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2038 = unembed_term t2  in
             FStar_Util.bind_opt uu____2038
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2047)::(post,uu____2049)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2084 = unembed_term pre  in
             FStar_Util.bind_opt uu____2084
               (fun pre1  ->
                  let uu____2090 = unembed_term post  in
                  FStar_Util.bind_opt uu____2090
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
         | uu____2114 ->
             ((let uu____2128 =
                 let uu____2133 =
                   let uu____2134 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2134
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2133)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2128);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2145 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2145 with
    | (hd1,args) ->
        let uu____2184 =
          let uu____2197 =
            let uu____2198 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2198.FStar_Syntax_Syntax.n  in
          (uu____2197, args)  in
        (match uu____2184 with
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
         | uu____2256 ->
             ((let uu____2270 =
                 let uu____2275 =
                   let uu____2276 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____2276
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2275)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2270);
              FStar_Pervasives_Native.None))
  
let (unembed_ctor :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.ctor FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2287 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2287 with
    | (hd1,args) ->
        let uu____2326 =
          let uu____2339 =
            let uu____2340 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2340.FStar_Syntax_Syntax.n  in
          (uu____2339, args)  in
        (match uu____2326 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2355)::(t2,uu____2357)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor.FStar_Reflection_Data.lid
             ->
             let uu____2392 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____2392
               (fun nm1  ->
                  let uu____2404 = unembed_term t2  in
                  FStar_Util.bind_opt uu____2404
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.Ctor (nm1, t3))))
         | uu____2413 ->
             ((let uu____2427 =
                 let uu____2432 =
                   let uu____2433 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded ctor: %s" uu____2433
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2432)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2427);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2444 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2444 with
    | (hd1,args) ->
        let uu____2483 =
          let uu____2496 =
            let uu____2497 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2497.FStar_Syntax_Syntax.n  in
          (uu____2496, args)  in
        (match uu____2483 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2512)::(bs,uu____2514)::(t2,uu____2516)::(dcs,uu____2518)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____2573 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____2573
               (fun nm1  ->
                  let uu____2585 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____2585
                    (fun bs1  ->
                       let uu____2591 = unembed_term t2  in
                       FStar_Util.bind_opt uu____2591
                         (fun t3  ->
                            let uu____2597 =
                              let uu____2602 =
                                FStar_Syntax_Embeddings.unembed_list
                                  unembed_ctor
                                 in
                              uu____2602 dcs  in
                            FStar_Util.bind_opt uu____2597
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____2623)::(ty,uu____2625)::(t2,uu____2627)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____2672 = unembed_fvar fvar1  in
             FStar_Util.bind_opt uu____2672
               (fun fvar2  ->
                  let uu____2678 = unembed_term ty  in
                  FStar_Util.bind_opt uu____2678
                    (fun ty1  ->
                       let uu____2684 = unembed_term t2  in
                       FStar_Util.bind_opt uu____2684
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_63  ->
                                 FStar_Pervasives_Native.Some _0_63)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____2706 ->
             ((let uu____2720 =
                 let uu____2725 =
                   let uu____2726 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____2726
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2725)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2720);
              FStar_Pervasives_Native.None))
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____2734 =
      let uu____2735 =
        let uu____2736 =
          let uu____2737 =
            let uu____2738 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____2741 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____2741 i.FStar_Syntax_Syntax.rng uu____2738  in
          FStar_Syntax_Syntax.as_arg uu____2737  in
        [uu____2736]  in
      FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv
        uu____2735
       in
    uu____2734 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 