open Prims
let (embed_bv :
  FStar_Range.range -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun bv  ->
      FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_binder
        FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
  
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
      let uu___51_39 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___51_39.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___51_39.FStar_Syntax_Syntax.vars)
      }
  
let (embed_binders :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun l  ->
      let uu____49 =
        FStar_Syntax_Embeddings.embed_list embed_binder
          FStar_Reflection_Data.fstar_refl_binder
         in
      uu____49 rng l
  
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
            let uu____95 =
              let uu____96 =
                let uu____97 =
                  let uu____98 =
                    let uu____99 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____99  in
                  FStar_Syntax_Syntax.as_arg uu____98  in
                [uu____97]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
                uu____96
               in
            uu____95 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____103 =
              let uu____104 =
                let uu____105 =
                  let uu____106 = FStar_Syntax_Embeddings.embed_string rng s
                     in
                  FStar_Syntax_Syntax.as_arg uu____106  in
                [uu____105]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
                uu____104
               in
            uu____103 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___52_109 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___52_109.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___52_109.FStar_Syntax_Syntax.vars)
      }
  
let rec (embed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedder) =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____118 =
            let uu____119 =
              let uu____120 =
                let uu____121 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____121  in
              [uu____120]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____119
             in
          uu____118 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____130 =
            let uu____131 =
              let uu____132 =
                let uu____133 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____133  in
              let uu____134 =
                let uu____137 =
                  let uu____138 =
                    let uu____139 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern
                       in
                    uu____139 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____138  in
                [uu____137]  in
              uu____132 :: uu____134  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____131
             in
          uu____130 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____150 =
            let uu____151 =
              let uu____152 =
                let uu____153 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____153  in
              [uu____152]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____151
             in
          uu____150 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____157 =
            let uu____158 =
              let uu____159 =
                let uu____160 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____160  in
              [uu____159]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____158
             in
          uu____157 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____165 =
            let uu____166 =
              let uu____167 =
                let uu____168 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____168  in
              let uu____169 =
                let uu____172 =
                  let uu____173 = embed_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____173  in
                [uu____172]  in
              uu____167 :: uu____169  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____166
             in
          uu____165 FStar_Pervasives_Native.None rng
  
let (embed_branch :
  FStar_Range.range ->
    FStar_Reflection_Data.branch -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun br  ->
      let uu____185 =
        FStar_Syntax_Embeddings.embed_pair embed_pattern
          FStar_Reflection_Data.fstar_refl_pattern embed_term
          FStar_Syntax_Syntax.t_term
         in
      uu____185 rng br
  
let (embed_argv :
  FStar_Range.range -> FStar_Reflection_Data.argv -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun aq  ->
      let uu____204 =
        FStar_Syntax_Embeddings.embed_pair embed_term
          FStar_Syntax_Syntax.t_term embed_aqualv
          FStar_Reflection_Data.fstar_refl_aqualv
         in
      uu____204 rng aq
  
let (embed_term_view :
  FStar_Range.range ->
    FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  ->
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____224 =
            let uu____225 =
              let uu____226 =
                let uu____227 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____227  in
              [uu____226]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____225
             in
          uu____224 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____231 =
            let uu____232 =
              let uu____233 =
                let uu____234 = embed_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____234  in
              [uu____233]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____232
             in
          uu____231 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____238 =
            let uu____239 =
              let uu____240 =
                let uu____241 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____241  in
              [uu____240]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____239
             in
          uu____238 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____246 =
            let uu____247 =
              let uu____248 =
                let uu____249 = embed_term rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____249  in
              let uu____250 =
                let uu____253 =
                  let uu____254 = embed_argv rng a  in
                  FStar_Syntax_Syntax.as_arg uu____254  in
                [uu____253]  in
              uu____248 :: uu____250  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____247
             in
          uu____246 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____259 =
            let uu____260 =
              let uu____261 =
                let uu____262 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____262  in
              let uu____263 =
                let uu____266 =
                  let uu____267 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____267  in
                [uu____266]  in
              uu____261 :: uu____263  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____260
             in
          uu____259 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____272 =
            let uu____273 =
              let uu____274 =
                let uu____275 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____275  in
              let uu____276 =
                let uu____279 =
                  let uu____280 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____280  in
                [uu____279]  in
              uu____274 :: uu____276  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____273
             in
          uu____272 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____284 =
            let uu____285 =
              let uu____286 =
                let uu____287 = FStar_Syntax_Embeddings.embed_unit rng ()  in
                FStar_Syntax_Syntax.as_arg uu____287  in
              [uu____286]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____285
             in
          uu____284 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____292 =
            let uu____293 =
              let uu____294 =
                let uu____295 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____295  in
              let uu____296 =
                let uu____299 =
                  let uu____300 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____300  in
                [uu____299]  in
              uu____294 :: uu____296  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____293
             in
          uu____292 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____304 =
            let uu____305 =
              let uu____306 =
                let uu____307 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____307  in
              [uu____306]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____305
             in
          uu____304 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____312 =
            let uu____313 =
              let uu____314 =
                let uu____315 = FStar_Syntax_Embeddings.embed_int rng u  in
                FStar_Syntax_Syntax.as_arg uu____315  in
              let uu____316 =
                let uu____319 =
                  let uu____320 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____320  in
                [uu____319]  in
              uu____314 :: uu____316  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____313
             in
          uu____312 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____327 =
            let uu____328 =
              let uu____329 =
                let uu____330 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____330  in
              let uu____331 =
                let uu____334 =
                  let uu____335 = embed_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____335  in
                let uu____336 =
                  let uu____339 =
                    let uu____340 = embed_term rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____340  in
                  let uu____341 =
                    let uu____344 =
                      let uu____345 = embed_term rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____345  in
                    [uu____344]  in
                  uu____339 :: uu____341  in
                uu____334 :: uu____336  in
              uu____329 :: uu____331  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____328
             in
          uu____327 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____354 =
            let uu____355 =
              let uu____356 =
                let uu____357 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____357  in
              let uu____358 =
                let uu____361 =
                  let uu____362 =
                    let uu____363 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____363 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____362  in
                [uu____361]  in
              uu____356 :: uu____358  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____355
             in
          uu____354 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___53_373 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___53_373.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___53_373.FStar_Syntax_Syntax.vars)
          }
  
let (embed_bv_view :
  FStar_Range.range ->
    FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun bvv  ->
      let uu____383 =
        let uu____384 =
          let uu____385 =
            let uu____386 =
              FStar_Syntax_Embeddings.embed_string rng
                bvv.FStar_Reflection_Data.bv_ppname
               in
            FStar_Syntax_Syntax.as_arg uu____386  in
          let uu____387 =
            let uu____390 =
              let uu____391 =
                FStar_Syntax_Embeddings.embed_int rng
                  bvv.FStar_Reflection_Data.bv_index
                 in
              FStar_Syntax_Syntax.as_arg uu____391  in
            let uu____392 =
              let uu____395 =
                let uu____396 =
                  embed_term rng bvv.FStar_Reflection_Data.bv_sort  in
                FStar_Syntax_Syntax.as_arg uu____396  in
              [uu____395]  in
            uu____390 :: uu____392  in
          uu____385 :: uu____387  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____384
         in
      uu____383 FStar_Pervasives_Native.None rng
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total (t,md) ->
          let uu____414 =
            let uu____415 =
              let uu____416 =
                let uu____417 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____417  in
              let uu____418 =
                let uu____421 =
                  let uu____422 =
                    let uu____423 =
                      FStar_Syntax_Embeddings.embed_option embed_term
                        FStar_Syntax_Syntax.t_term
                       in
                    uu____423 rng md  in
                  FStar_Syntax_Syntax.as_arg uu____422  in
                [uu____421]  in
              uu____416 :: uu____418  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____415
             in
          uu____414 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____438 =
            let uu____439 =
              let uu____440 =
                let uu____441 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____441  in
              let uu____442 =
                let uu____445 =
                  let uu____446 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____446  in
                [uu____445]  in
              uu____440 :: uu____442  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____439
             in
          uu____438 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___54_449 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___54_449.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___54_449.FStar_Syntax_Syntax.vars)
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
      let uu___55_460 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_460.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_460.FStar_Syntax_Syntax.vars)
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
      | FStar_Reflection_Data.Sg_Let (r,fv,ty,t) ->
          let uu____483 =
            let uu____484 =
              let uu____485 =
                let uu____486 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____486  in
              let uu____487 =
                let uu____490 =
                  let uu____491 = embed_fvar rng fv  in
                  FStar_Syntax_Syntax.as_arg uu____491  in
                let uu____492 =
                  let uu____495 =
                    let uu____496 = embed_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____496  in
                  let uu____497 =
                    let uu____500 =
                      let uu____501 = embed_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____501  in
                    [uu____500]  in
                  uu____495 :: uu____497  in
                uu____490 :: uu____492  in
              uu____485 :: uu____487  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____484
             in
          uu____483 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
          let uu____506 =
            let uu____507 =
              let uu____508 =
                let uu____509 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____509  in
              let uu____510 =
                let uu____513 =
                  let uu____514 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____514  in
                [uu____513]  in
              uu____508 :: uu____510  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
              uu____507
             in
          uu____506 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____529 =
            let uu____530 =
              let uu____531 =
                let uu____532 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____532  in
              let uu____533 =
                let uu____536 =
                  let uu____537 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____537  in
                let uu____538 =
                  let uu____541 =
                    let uu____542 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____542  in
                  let uu____543 =
                    let uu____546 =
                      let uu____547 =
                        let uu____548 =
                          let uu____555 =
                            FStar_Syntax_Syntax.t_list_of
                              FStar_Syntax_Syntax.t_string
                             in
                          FStar_Syntax_Embeddings.embed_list
                            FStar_Syntax_Embeddings.embed_string_list
                            uu____555
                           in
                        uu____548 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____547  in
                    [uu____546]  in
                  uu____541 :: uu____543  in
                uu____536 :: uu____538  in
              uu____531 :: uu____533  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____530
             in
          uu____529 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___56_563 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___56_563.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___56_563.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_bv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____573 =
      let uu____574 = FStar_Syntax_Subst.compress t  in
      uu____574.FStar_Syntax_Syntax.n  in
    match uu____573 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____580 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____580
    | uu____581 ->
        ((let uu____583 =
            let uu____588 =
              let uu____589 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____589  in
            (FStar_Errors.Warning_NotEmbedded, uu____588)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____583);
         FStar_Pervasives_Native.None)
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____599 =
      let uu____600 = FStar_Syntax_Subst.compress t  in
      uu____600.FStar_Syntax_Syntax.n  in
    match uu____599 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____606 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____606
    | uu____607 ->
        ((let uu____609 =
            let uu____614 =
              let uu____615 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____615  in
            (FStar_Errors.Warning_NotEmbedded, uu____614)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____609);
         FStar_Pervasives_Native.None)
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____626;
           FStar_Syntax_Syntax.pos = uu____627;
           FStar_Syntax_Syntax.vars = uu____628;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> FStar_Pervasives_Native.Some qt
    | uu____641 ->
        ((let uu____643 =
            let uu____648 =
              let uu____649 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____649  in
            (FStar_Errors.Warning_NotEmbedded, uu____648)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____643);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____660 = FStar_Syntax_Util.head_and_args t1  in
    match uu____660 with
    | (hd1,args) ->
        let uu____699 =
          let uu____712 =
            let uu____713 = FStar_Syntax_Util.un_uinst hd1  in
            uu____713.FStar_Syntax_Syntax.n  in
          (uu____712, args)  in
        (match uu____699 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____756 ->
             ((let uu____770 =
                 let uu____775 =
                   let uu____776 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____776
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____775)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____770);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____784 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____784 t
  
let (unembed_fvar :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____800 =
      let uu____801 = FStar_Syntax_Subst.compress t  in
      uu____801.FStar_Syntax_Syntax.n  in
    match uu____800 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____807 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____807
    | uu____808 ->
        ((let uu____810 =
            let uu____815 =
              let uu____816 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____816  in
            (FStar_Errors.Warning_NotEmbedded, uu____815)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____810);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____826 =
      let uu____827 = FStar_Syntax_Subst.compress t  in
      uu____827.FStar_Syntax_Syntax.n  in
    match uu____826 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____833 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____833
    | uu____834 ->
        ((let uu____836 =
            let uu____841 =
              let uu____842 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____842  in
            (FStar_Errors.Warning_NotEmbedded, uu____841)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____836);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____852 =
      let uu____853 = FStar_Syntax_Subst.compress t  in
      uu____853.FStar_Syntax_Syntax.n  in
    match uu____852 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____859 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____859
    | uu____860 ->
        ((let uu____862 =
            let uu____867 =
              let uu____868 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____868  in
            (FStar_Errors.Warning_NotEmbedded, uu____867)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____862);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____879 = FStar_Syntax_Util.head_and_args t1  in
    match uu____879 with
    | (hd1,args) ->
        let uu____918 =
          let uu____931 =
            let uu____932 = FStar_Syntax_Util.un_uinst hd1  in
            uu____932.FStar_Syntax_Syntax.n  in
          (uu____931, args)  in
        (match uu____918 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____992)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1017 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____1017
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1026)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1051 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____1051
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1058 ->
             ((let uu____1072 =
                 let uu____1077 =
                   let uu____1078 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____1078
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1077)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1072);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1087 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1087 with
    | (hd1,args) ->
        let uu____1126 =
          let uu____1139 =
            let uu____1140 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1140.FStar_Syntax_Syntax.n  in
          (uu____1139, args)  in
        (match uu____1126 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1155)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1180 = unembed_const c  in
             FStar_Util.bind_opt uu____1180
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1189)::(ps,uu____1191)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1226 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1226
               (fun f1  ->
                  let uu____1232 =
                    let uu____1237 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1237 ps  in
                  FStar_Util.bind_opt uu____1232
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1256)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1281 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1281
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var bv1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1290)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1315 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1315
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild bv1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(bv,uu____1324)::(t2,uu____1326)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
             ->
             let uu____1361 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1361
               (fun bv1  ->
                  let uu____1367 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1367
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                         (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
         | uu____1374 ->
             ((let uu____1388 =
                 let uu____1393 =
                   let uu____1394 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1394
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1393)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1388);
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
    let uu____1425 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1425 with
    | (hd1,args) ->
        let uu____1464 =
          let uu____1477 =
            let uu____1478 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1478.FStar_Syntax_Syntax.n  in
          (uu____1477, args)  in
        (match uu____1464 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1493)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1518 = unembed_bv b  in
             FStar_Util.bind_opt uu____1518
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1527)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
             ->
             let uu____1552 = unembed_bv b  in
             FStar_Util.bind_opt uu____1552
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                    (FStar_Reflection_Data.Tv_BVar b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1561)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1586 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1586
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1595)::(r,uu____1597)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1632 = unembed_term l  in
             FStar_Util.bind_opt uu____1632
               (fun l1  ->
                  let uu____1638 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1638
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1663)::(t2,uu____1665)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1700 = unembed_binder b  in
             FStar_Util.bind_opt uu____1700
               (fun b1  ->
                  let uu____1706 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1706
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1715)::(t2,uu____1717)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1752 = unembed_binder b  in
             FStar_Util.bind_opt uu____1752
               (fun b1  ->
                  let uu____1758 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1758
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1767)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1792 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1792
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1801)::(t2,uu____1803)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1838 = unembed_bv b  in
             FStar_Util.bind_opt uu____1838
               (fun b1  ->
                  let uu____1844 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1844
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1853)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1878 = unembed_const c  in
             FStar_Util.bind_opt uu____1878
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1887)::(t2,uu____1889)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1924 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1924
               (fun u1  ->
                  let uu____1930 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1930
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_56  -> FStar_Pervasives_Native.Some _0_56)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____1939)::(b,uu____1941)::(t11,uu____1943)::(t2,uu____1945)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____2000 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____2000
               (fun r1  ->
                  let uu____2006 = unembed_bv b  in
                  FStar_Util.bind_opt uu____2006
                    (fun b1  ->
                       let uu____2012 = unembed_term t11  in
                       FStar_Util.bind_opt uu____2012
                         (fun t12  ->
                            let uu____2018 = unembed_term t2  in
                            FStar_Util.bind_opt uu____2018
                              (fun t21  ->
                                 FStar_All.pipe_left
                                   (fun _0_57  ->
                                      FStar_Pervasives_Native.Some _0_57)
                                   (FStar_Reflection_Data.Tv_Let
                                      (r1, b1, t12, t21))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2027)::(brs,uu____2029)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____2064 = unembed_term t2  in
             FStar_Util.bind_opt uu____2064
               (fun t3  ->
                  let uu____2070 =
                    let uu____2079 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____2079 brs  in
                  FStar_Util.bind_opt uu____2070
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                         (FStar_Reflection_Data.Tv_Match (t3, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_59  -> FStar_Pervasives_Native.Some _0_59)
               FStar_Reflection_Data.Tv_Unknown
         | uu____2133 ->
             ((let uu____2147 =
                 let uu____2152 =
                   let uu____2153 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____2153
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2152)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2147);
              FStar_Pervasives_Native.None))
  
let (unembed_bv_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.bv_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2164 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2164 with
    | (hd1,args) ->
        let uu____2203 =
          let uu____2216 =
            let uu____2217 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2217.FStar_Syntax_Syntax.n  in
          (uu____2216, args)  in
        (match uu____2203 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2232)::(idx,uu____2234)::(s,uu____2236)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2281 = FStar_Syntax_Embeddings.unembed_string nm  in
             FStar_Util.bind_opt uu____2281
               (fun nm1  ->
                  let uu____2287 = FStar_Syntax_Embeddings.unembed_int idx
                     in
                  FStar_Util.bind_opt uu____2287
                    (fun idx1  ->
                       let uu____2293 = unembed_term s  in
                       FStar_Util.bind_opt uu____2293
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_60  ->
                                 FStar_Pervasives_Native.Some _0_60)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2300 ->
             ((let uu____2314 =
                 let uu____2319 =
                   let uu____2320 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded bv_view: %s"
                     uu____2320
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2319)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2314);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2331 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2331 with
    | (hd1,args) ->
        let uu____2370 =
          let uu____2383 =
            let uu____2384 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2384.FStar_Syntax_Syntax.n  in
          (uu____2383, args)  in
        (match uu____2370 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2399)::(md,uu____2401)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2436 = unembed_term t2  in
             FStar_Util.bind_opt uu____2436
               (fun t3  ->
                  let uu____2442 =
                    let uu____2447 =
                      FStar_Syntax_Embeddings.unembed_option unembed_term  in
                    uu____2447 md  in
                  FStar_Util.bind_opt uu____2442
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2466)::(post,uu____2468)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2503 = unembed_term pre  in
             FStar_Util.bind_opt uu____2503
               (fun pre1  ->
                  let uu____2509 = unembed_term post  in
                  FStar_Util.bind_opt uu____2509
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_62  -> FStar_Pervasives_Native.Some _0_62)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_63  -> FStar_Pervasives_Native.Some _0_63)
               FStar_Reflection_Data.C_Unknown
         | uu____2533 ->
             ((let uu____2547 =
                 let uu____2552 =
                   let uu____2553 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2553
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2552)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2547);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2564 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2564 with
    | (hd1,args) ->
        let uu____2603 =
          let uu____2616 =
            let uu____2617 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2617.FStar_Syntax_Syntax.n  in
          (uu____2616, args)  in
        (match uu____2603 with
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
         | uu____2675 ->
             ((let uu____2689 =
                 let uu____2694 =
                   let uu____2695 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____2695
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2694)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2689);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____2705 =
      let uu____2706 = FStar_Syntax_Subst.compress t  in
      uu____2706.FStar_Syntax_Syntax.n  in
    match uu____2705 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____2712 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____2712
    | uu____2713 ->
        ((let uu____2715 =
            let uu____2720 =
              let uu____2721 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____2721  in
            (FStar_Errors.Warning_NotEmbedded, uu____2720)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2715);
         FStar_Pervasives_Native.None)
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2732 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2732 with
    | (hd1,args) ->
        let uu____2771 =
          let uu____2784 =
            let uu____2785 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2785.FStar_Syntax_Syntax.n  in
          (uu____2784, args)  in
        (match uu____2771 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2800)::(bs,uu____2802)::(t2,uu____2804)::(dcs,uu____2806)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____2861 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____2861
               (fun nm1  ->
                  let uu____2873 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____2873
                    (fun bs1  ->
                       let uu____2879 = unembed_term t2  in
                       FStar_Util.bind_opt uu____2879
                         (fun t3  ->
                            let uu____2885 =
                              let uu____2892 =
                                let uu____2899 =
                                  FStar_Syntax_Embeddings.unembed_list
                                    FStar_Syntax_Embeddings.unembed_string
                                   in
                                FStar_Syntax_Embeddings.unembed_list
                                  uu____2899
                                 in
                              uu____2892 dcs  in
                            FStar_Util.bind_opt uu____2885
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_Pervasives_Native.Some _0_64)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____2932)::(fvar1,uu____2934)::(ty,uu____2936)::(t2,uu____2938)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____2993 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____2993
               (fun r1  ->
                  let uu____2999 = unembed_fvar fvar1  in
                  FStar_Util.bind_opt uu____2999
                    (fun fvar2  ->
                       let uu____3005 = unembed_term ty  in
                       FStar_Util.bind_opt uu____3005
                         (fun ty1  ->
                            let uu____3011 = unembed_term t2  in
                            FStar_Util.bind_opt uu____3011
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_65  ->
                                      FStar_Pervasives_Native.Some _0_65)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____3033 ->
             ((let uu____3047 =
                 let uu____3052 =
                   let uu____3053 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____3053
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3052)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3047);
              FStar_Pervasives_Native.None))
  
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3064 =
      let uu____3065 =
        let uu____3066 =
          let uu____3067 =
            let uu____3068 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____3071 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____3071 i.FStar_Syntax_Syntax.rng uu____3068  in
          FStar_Syntax_Syntax.as_arg uu____3067  in
        [uu____3066]  in
      FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv
        uu____3065
       in
    uu____3064 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 