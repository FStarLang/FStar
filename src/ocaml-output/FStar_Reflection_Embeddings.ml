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
  
let (embed_sigelt :
  FStar_Range.range -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun se  ->
      FStar_Syntax_Util.mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
        FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng)
  
let (embed_sigelt_view :
  FStar_Range.range ->
    FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun sev  ->
      match sev with
      | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
          let uu____404 =
            let uu____405 =
              let uu____406 =
                let uu____407 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____407  in
              let uu____408 =
                let uu____411 =
                  let uu____412 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____412  in
                let uu____413 =
                  let uu____416 =
                    let uu____417 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____417  in
                  [uu____416]  in
                uu____411 :: uu____413  in
              uu____406 :: uu____408  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____405
             in
          uu____404 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
          let uu____422 =
            let uu____423 =
              let uu____424 =
                let uu____425 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____425  in
              let uu____426 =
                let uu____429 =
                  let uu____430 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____430  in
                [uu____429]  in
              uu____424 :: uu____426  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
              uu____423
             in
          uu____422 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____445 =
            let uu____446 =
              let uu____447 =
                let uu____448 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____448  in
              let uu____449 =
                let uu____452 =
                  let uu____453 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____453  in
                let uu____454 =
                  let uu____457 =
                    let uu____458 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____458  in
                  let uu____459 =
                    let uu____462 =
                      let uu____463 =
                        let uu____464 =
                          let uu____471 =
                            FStar_Syntax_Syntax.t_list_of
                              FStar_Syntax_Syntax.t_string
                             in
                          FStar_Syntax_Embeddings.embed_list
                            FStar_Syntax_Embeddings.embed_string_list
                            uu____471
                           in
                        uu____464 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____463  in
                    [uu____462]  in
                  uu____457 :: uu____459  in
                uu____452 :: uu____454  in
              uu____447 :: uu____449  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____446
             in
          uu____445 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___56_479 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___56_479.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___56_479.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____489 =
      let uu____490 = FStar_Syntax_Subst.compress t  in
      uu____490.FStar_Syntax_Syntax.n  in
    match uu____489 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____496 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____496
    | uu____497 ->
        ((let uu____499 =
            let uu____504 =
              let uu____505 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____505  in
            (FStar_Errors.Warning_NotEmbedded, uu____504)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____499);
         FStar_Pervasives_Native.None)
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____516;
           FStar_Syntax_Syntax.pos = uu____517;
           FStar_Syntax_Syntax.vars = uu____518;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> FStar_Pervasives_Native.Some qt
    | uu____531 ->
        ((let uu____533 =
            let uu____538 =
              let uu____539 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____539  in
            (FStar_Errors.Warning_NotEmbedded, uu____538)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____533);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____550 = FStar_Syntax_Util.head_and_args t1  in
    match uu____550 with
    | (hd1,args) ->
        let uu____589 =
          let uu____602 =
            let uu____603 = FStar_Syntax_Util.un_uinst hd1  in
            uu____603.FStar_Syntax_Syntax.n  in
          (uu____602, args)  in
        (match uu____589 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____646 ->
             ((let uu____660 =
                 let uu____665 =
                   let uu____666 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____666
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____665)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____660);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____674 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____674 t
  
let (unembed_fvar :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____690 =
      let uu____691 = FStar_Syntax_Subst.compress t  in
      uu____691.FStar_Syntax_Syntax.n  in
    match uu____690 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____697 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____697
    | uu____698 ->
        ((let uu____700 =
            let uu____705 =
              let uu____706 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____706  in
            (FStar_Errors.Warning_NotEmbedded, uu____705)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____700);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____716 =
      let uu____717 = FStar_Syntax_Subst.compress t  in
      uu____717.FStar_Syntax_Syntax.n  in
    match uu____716 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____723 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____723
    | uu____724 ->
        ((let uu____726 =
            let uu____731 =
              let uu____732 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____732  in
            (FStar_Errors.Warning_NotEmbedded, uu____731)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____726);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____742 =
      let uu____743 = FStar_Syntax_Subst.compress t  in
      uu____743.FStar_Syntax_Syntax.n  in
    match uu____742 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____749 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____749
    | uu____750 ->
        ((let uu____752 =
            let uu____757 =
              let uu____758 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____758  in
            (FStar_Errors.Warning_NotEmbedded, uu____757)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____752);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____769 = FStar_Syntax_Util.head_and_args t1  in
    match uu____769 with
    | (hd1,args) ->
        let uu____808 =
          let uu____821 =
            let uu____822 = FStar_Syntax_Util.un_uinst hd1  in
            uu____822.FStar_Syntax_Syntax.n  in
          (uu____821, args)  in
        (match uu____808 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____882)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____907 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____907
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____916)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____941 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____941
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____948 ->
             ((let uu____962 =
                 let uu____967 =
                   let uu____968 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____968
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____967)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____962);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____977 = FStar_Syntax_Util.head_and_args t1  in
    match uu____977 with
    | (hd1,args) ->
        let uu____1016 =
          let uu____1029 =
            let uu____1030 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1030.FStar_Syntax_Syntax.n  in
          (uu____1029, args)  in
        (match uu____1016 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1045)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1070 = unembed_const c  in
             FStar_Util.bind_opt uu____1070
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1079)::(ps,uu____1081)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1116 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1116
               (fun f1  ->
                  let uu____1122 =
                    let uu____1127 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1127 ps  in
                  FStar_Util.bind_opt uu____1122
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1146)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1171 = unembed_binder b  in
             FStar_Util.bind_opt uu____1171
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1180)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1205 = unembed_binder b  in
             FStar_Util.bind_opt uu____1205
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild b1))
         | uu____1212 ->
             ((let uu____1226 =
                 let uu____1231 =
                   let uu____1232 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1232
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1231)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1226);
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
    let uu____1263 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1263 with
    | (hd1,args) ->
        let uu____1302 =
          let uu____1315 =
            let uu____1316 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1316.FStar_Syntax_Syntax.n  in
          (uu____1315, args)  in
        (match uu____1302 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1331)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1356 = unembed_binder b  in
             FStar_Util.bind_opt uu____1356
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1365)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1390 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1390
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1399)::(r,uu____1401)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1436 = unembed_term l  in
             FStar_Util.bind_opt uu____1436
               (fun l1  ->
                  let uu____1442 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1442
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1467)::(t2,uu____1469)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1504 = unembed_binder b  in
             FStar_Util.bind_opt uu____1504
               (fun b1  ->
                  let uu____1510 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1510
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1519)::(t2,uu____1521)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1556 = unembed_binder b  in
             FStar_Util.bind_opt uu____1556
               (fun b1  ->
                  let uu____1562 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1562
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1571)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1596 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1596
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1605)::(t2,uu____1607)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1642 = unembed_binder b  in
             FStar_Util.bind_opt uu____1642
               (fun b1  ->
                  let uu____1648 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1648
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1657)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1682 = unembed_const c  in
             FStar_Util.bind_opt uu____1682
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1691)::(t2,uu____1693)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1728 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1728
               (fun u1  ->
                  let uu____1734 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1734
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1743)::(t11,uu____1745)::(t2,uu____1747)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____1792 = unembed_binder b  in
             FStar_Util.bind_opt uu____1792
               (fun b1  ->
                  let uu____1798 = unembed_term t11  in
                  FStar_Util.bind_opt uu____1798
                    (fun t12  ->
                       let uu____1804 = unembed_term t2  in
                       FStar_Util.bind_opt uu____1804
                         (fun t21  ->
                            FStar_All.pipe_left
                              (fun _0_55  ->
                                 FStar_Pervasives_Native.Some _0_55)
                              (FStar_Reflection_Data.Tv_Let (b1, t12, t21)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1813)::(brs,uu____1815)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____1850 = unembed_term t2  in
             FStar_Util.bind_opt uu____1850
               (fun t3  ->
                  let uu____1856 =
                    let uu____1865 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____1865 brs  in
                  FStar_Util.bind_opt uu____1856
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
         | uu____1919 ->
             ((let uu____1933 =
                 let uu____1938 =
                   let uu____1939 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____1939
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1938)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1933);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1950 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1950 with
    | (hd1,args) ->
        let uu____1989 =
          let uu____2002 =
            let uu____2003 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2003.FStar_Syntax_Syntax.n  in
          (uu____2002, args)  in
        (match uu____1989 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____2018)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2043 = unembed_term t2  in
             FStar_Util.bind_opt uu____2043
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2052)::(post,uu____2054)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2089 = unembed_term pre  in
             FStar_Util.bind_opt uu____2089
               (fun pre1  ->
                  let uu____2095 = unembed_term post  in
                  FStar_Util.bind_opt uu____2095
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
         | uu____2119 ->
             ((let uu____2133 =
                 let uu____2138 =
                   let uu____2139 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2139
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2138)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2133);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2150 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2150 with
    | (hd1,args) ->
        let uu____2189 =
          let uu____2202 =
            let uu____2203 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2203.FStar_Syntax_Syntax.n  in
          (uu____2202, args)  in
        (match uu____2189 with
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
         | uu____2261 ->
             ((let uu____2275 =
                 let uu____2280 =
                   let uu____2281 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____2281
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2280)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2275);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____2291 =
      let uu____2292 = FStar_Syntax_Subst.compress t  in
      uu____2292.FStar_Syntax_Syntax.n  in
    match uu____2291 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____2298 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____2298
    | uu____2299 ->
        ((let uu____2301 =
            let uu____2306 =
              let uu____2307 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____2307  in
            (FStar_Errors.Warning_NotEmbedded, uu____2306)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2301);
         FStar_Pervasives_Native.None)
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2318 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2318 with
    | (hd1,args) ->
        let uu____2357 =
          let uu____2370 =
            let uu____2371 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2371.FStar_Syntax_Syntax.n  in
          (uu____2370, args)  in
        (match uu____2357 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2386)::(bs,uu____2388)::(t2,uu____2390)::(dcs,uu____2392)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____2447 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____2447
               (fun nm1  ->
                  let uu____2459 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____2459
                    (fun bs1  ->
                       let uu____2465 = unembed_term t2  in
                       FStar_Util.bind_opt uu____2465
                         (fun t3  ->
                            let uu____2471 =
                              let uu____2478 =
                                let uu____2485 =
                                  FStar_Syntax_Embeddings.unembed_list
                                    FStar_Syntax_Embeddings.unembed_string
                                   in
                                FStar_Syntax_Embeddings.unembed_list
                                  uu____2485
                                 in
                              uu____2478 dcs  in
                            FStar_Util.bind_opt uu____2471
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_Pervasives_Native.Some _0_61)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____2518)::(ty,uu____2520)::(t2,uu____2522)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____2567 = unembed_fvar fvar1  in
             FStar_Util.bind_opt uu____2567
               (fun fvar2  ->
                  let uu____2573 = unembed_term ty  in
                  FStar_Util.bind_opt uu____2573
                    (fun ty1  ->
                       let uu____2579 = unembed_term t2  in
                       FStar_Util.bind_opt uu____2579
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_62  ->
                                 FStar_Pervasives_Native.Some _0_62)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____2601 ->
             ((let uu____2615 =
                 let uu____2620 =
                   let uu____2621 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____2621
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2620)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2615);
              FStar_Pervasives_Native.None))
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____2629 =
      let uu____2630 =
        let uu____2631 =
          let uu____2632 =
            let uu____2633 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____2636 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____2636 i.FStar_Syntax_Syntax.rng uu____2633  in
          FStar_Syntax_Syntax.as_arg uu____2632  in
        [uu____2631]  in
      FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv
        uu____2630
       in
    uu____2629 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 