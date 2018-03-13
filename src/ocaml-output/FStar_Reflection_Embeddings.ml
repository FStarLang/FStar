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
  
let (embed_fv :
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
                let uu____133 = embed_fv rng fv  in
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
                let uu____227 = embed_fv rng fv  in
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
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____380 =
            let uu____381 =
              let uu____382 =
                let uu____383 = embed_term rng e  in
                FStar_Syntax_Syntax.as_arg uu____383  in
              let uu____384 =
                let uu____387 =
                  let uu____388 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____388  in
                let uu____389 =
                  let uu____392 =
                    let uu____393 =
                      let uu____394 =
                        FStar_Syntax_Embeddings.embed_option embed_term
                          FStar_Reflection_Data.fstar_refl_term
                         in
                      uu____394 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____393  in
                  [uu____392]  in
                uu____387 :: uu____389  in
              uu____382 :: uu____384  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____381
             in
          uu____380 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____411 =
            let uu____412 =
              let uu____413 =
                let uu____414 = embed_term rng e  in
                FStar_Syntax_Syntax.as_arg uu____414  in
              let uu____415 =
                let uu____418 =
                  let uu____419 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____419  in
                let uu____420 =
                  let uu____423 =
                    let uu____424 =
                      let uu____425 =
                        FStar_Syntax_Embeddings.embed_option embed_term
                          FStar_Reflection_Data.fstar_refl_term
                         in
                      uu____425 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____424  in
                  [uu____423]  in
                uu____418 :: uu____420  in
              uu____413 :: uu____415  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____412
             in
          uu____411 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___53_435 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___53_435.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___53_435.FStar_Syntax_Syntax.vars)
          }
  
let (embed_bv_view :
  FStar_Range.range ->
    FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun bvv  ->
      let uu____445 =
        let uu____446 =
          let uu____447 =
            let uu____448 =
              FStar_Syntax_Embeddings.embed_string rng
                bvv.FStar_Reflection_Data.bv_ppname
               in
            FStar_Syntax_Syntax.as_arg uu____448  in
          let uu____449 =
            let uu____452 =
              let uu____453 =
                FStar_Syntax_Embeddings.embed_int rng
                  bvv.FStar_Reflection_Data.bv_index
                 in
              FStar_Syntax_Syntax.as_arg uu____453  in
            let uu____454 =
              let uu____457 =
                let uu____458 =
                  embed_term rng bvv.FStar_Reflection_Data.bv_sort  in
                FStar_Syntax_Syntax.as_arg uu____458  in
              [uu____457]  in
            uu____452 :: uu____454  in
          uu____447 :: uu____449  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____446
         in
      uu____445 FStar_Pervasives_Native.None rng
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total (t,md) ->
          let uu____476 =
            let uu____477 =
              let uu____478 =
                let uu____479 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____479  in
              let uu____480 =
                let uu____483 =
                  let uu____484 =
                    let uu____485 =
                      FStar_Syntax_Embeddings.embed_option embed_term
                        FStar_Syntax_Syntax.t_term
                       in
                    uu____485 rng md  in
                  FStar_Syntax_Syntax.as_arg uu____484  in
                [uu____483]  in
              uu____478 :: uu____480  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____477
             in
          uu____476 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____500 =
            let uu____501 =
              let uu____502 =
                let uu____503 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____503  in
              let uu____504 =
                let uu____507 =
                  let uu____508 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____508  in
                [uu____507]  in
              uu____502 :: uu____504  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____501
             in
          uu____500 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___54_511 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___54_511.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___54_511.FStar_Syntax_Syntax.vars)
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
      let uu___55_522 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_522.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_522.FStar_Syntax_Syntax.vars)
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
          let uu____545 =
            let uu____546 =
              let uu____547 =
                let uu____548 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____548  in
              let uu____549 =
                let uu____552 =
                  let uu____553 = embed_fv rng fv  in
                  FStar_Syntax_Syntax.as_arg uu____553  in
                let uu____554 =
                  let uu____557 =
                    let uu____558 = embed_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____558  in
                  let uu____559 =
                    let uu____562 =
                      let uu____563 = embed_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____563  in
                    [uu____562]  in
                  uu____557 :: uu____559  in
                uu____552 :: uu____554  in
              uu____547 :: uu____549  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____546
             in
          uu____545 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
          let uu____568 =
            let uu____569 =
              let uu____570 =
                let uu____571 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____571  in
              let uu____572 =
                let uu____575 =
                  let uu____576 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____576  in
                [uu____575]  in
              uu____570 :: uu____572  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
              uu____569
             in
          uu____568 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____591 =
            let uu____592 =
              let uu____593 =
                let uu____594 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____594  in
              let uu____595 =
                let uu____598 =
                  let uu____599 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____599  in
                let uu____600 =
                  let uu____603 =
                    let uu____604 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____604  in
                  let uu____605 =
                    let uu____608 =
                      let uu____609 =
                        let uu____610 =
                          let uu____617 =
                            FStar_Syntax_Syntax.t_list_of
                              FStar_Syntax_Syntax.t_string
                             in
                          FStar_Syntax_Embeddings.embed_list
                            FStar_Syntax_Embeddings.embed_string_list
                            uu____617
                           in
                        uu____610 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____609  in
                    [uu____608]  in
                  uu____603 :: uu____605  in
                uu____598 :: uu____600  in
              uu____593 :: uu____595  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____592
             in
          uu____591 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___56_625 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___56_625.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___56_625.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_bv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____635 =
      let uu____636 = FStar_Syntax_Subst.compress t  in
      uu____636.FStar_Syntax_Syntax.n  in
    match uu____635 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____642 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____642
    | uu____643 ->
        ((let uu____645 =
            let uu____650 =
              let uu____651 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____651  in
            (FStar_Errors.Warning_NotEmbedded, uu____650)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____645);
         FStar_Pervasives_Native.None)
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____661 =
      let uu____662 = FStar_Syntax_Subst.compress t  in
      uu____662.FStar_Syntax_Syntax.n  in
    match uu____661 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____668 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____668
    | uu____669 ->
        ((let uu____671 =
            let uu____676 =
              let uu____677 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____677  in
            (FStar_Errors.Warning_NotEmbedded, uu____676)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____671);
         FStar_Pervasives_Native.None)
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____688;
           FStar_Syntax_Syntax.pos = uu____689;
           FStar_Syntax_Syntax.vars = uu____690;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> FStar_Pervasives_Native.Some qt
    | uu____703 ->
        ((let uu____705 =
            let uu____710 =
              let uu____711 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____711  in
            (FStar_Errors.Warning_NotEmbedded, uu____710)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____705);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____722 = FStar_Syntax_Util.head_and_args t1  in
    match uu____722 with
    | (hd1,args) ->
        let uu____761 =
          let uu____774 =
            let uu____775 = FStar_Syntax_Util.un_uinst hd1  in
            uu____775.FStar_Syntax_Syntax.n  in
          (uu____774, args)  in
        (match uu____761 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____818 ->
             ((let uu____832 =
                 let uu____837 =
                   let uu____838 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____838
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____837)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____832);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____846 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____846 t
  
let (unembed_fv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____862 =
      let uu____863 = FStar_Syntax_Subst.compress t  in
      uu____863.FStar_Syntax_Syntax.n  in
    match uu____862 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____869 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____869
    | uu____870 ->
        ((let uu____872 =
            let uu____877 =
              let uu____878 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____878  in
            (FStar_Errors.Warning_NotEmbedded, uu____877)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____872);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____888 =
      let uu____889 = FStar_Syntax_Subst.compress t  in
      uu____889.FStar_Syntax_Syntax.n  in
    match uu____888 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____895 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____895
    | uu____896 ->
        ((let uu____898 =
            let uu____903 =
              let uu____904 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____904  in
            (FStar_Errors.Warning_NotEmbedded, uu____903)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____898);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____914 =
      let uu____915 = FStar_Syntax_Subst.compress t  in
      uu____915.FStar_Syntax_Syntax.n  in
    match uu____914 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____921 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____921
    | uu____922 ->
        ((let uu____924 =
            let uu____929 =
              let uu____930 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____930  in
            (FStar_Errors.Warning_NotEmbedded, uu____929)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____924);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____941 = FStar_Syntax_Util.head_and_args t1  in
    match uu____941 with
    | (hd1,args) ->
        let uu____980 =
          let uu____993 =
            let uu____994 = FStar_Syntax_Util.un_uinst hd1  in
            uu____994.FStar_Syntax_Syntax.n  in
          (uu____993, args)  in
        (match uu____980 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1054)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1079 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____1079
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1088)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1113 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____1113
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1120 ->
             ((let uu____1134 =
                 let uu____1139 =
                   let uu____1140 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____1140
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1139)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1134);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1149 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1149 with
    | (hd1,args) ->
        let uu____1188 =
          let uu____1201 =
            let uu____1202 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1202.FStar_Syntax_Syntax.n  in
          (uu____1201, args)  in
        (match uu____1188 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1217)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1242 = unembed_const c  in
             FStar_Util.bind_opt uu____1242
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1251)::(ps,uu____1253)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1288 = unembed_fv f  in
             FStar_Util.bind_opt uu____1288
               (fun f1  ->
                  let uu____1294 =
                    let uu____1299 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1299 ps  in
                  FStar_Util.bind_opt uu____1294
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1318)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1343 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1343
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var bv1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1352)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1377 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1377
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild bv1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(bv,uu____1386)::(t2,uu____1388)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
             ->
             let uu____1423 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1423
               (fun bv1  ->
                  let uu____1429 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1429
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                         (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
         | uu____1436 ->
             ((let uu____1450 =
                 let uu____1455 =
                   let uu____1456 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1456
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1455)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1450);
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
    let uu____1486 = FStar_Syntax_Util.head_and_args t  in
    match uu____1486 with
    | (hd1,args) ->
        let uu____1525 =
          let uu____1538 =
            let uu____1539 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1539.FStar_Syntax_Syntax.n  in
          (uu____1538, args)  in
        (match uu____1525 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1554)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1579 = unembed_bv b  in
             FStar_Util.bind_opt uu____1579
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1588)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
             ->
             let uu____1613 = unembed_bv b  in
             FStar_Util.bind_opt uu____1613
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                    (FStar_Reflection_Data.Tv_BVar b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1622)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1647 = unembed_fv f  in
             FStar_Util.bind_opt uu____1647
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1656)::(r,uu____1658)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1693 = unembed_term l  in
             FStar_Util.bind_opt uu____1693
               (fun l1  ->
                  let uu____1699 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1699
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1724)::(t1,uu____1726)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1761 = unembed_binder b  in
             FStar_Util.bind_opt uu____1761
               (fun b1  ->
                  let uu____1767 = unembed_term t1  in
                  FStar_Util.bind_opt uu____1767
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                         (FStar_Reflection_Data.Tv_Abs (b1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1776)::(t1,uu____1778)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1813 = unembed_binder b  in
             FStar_Util.bind_opt uu____1813
               (fun b1  ->
                  let uu____1819 = unembed_comp t1  in
                  FStar_Util.bind_opt uu____1819
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1828)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1853 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1853
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1862)::(t1,uu____1864)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1899 = unembed_bv b  in
             FStar_Util.bind_opt uu____1899
               (fun b1  ->
                  let uu____1905 = unembed_term t1  in
                  FStar_Util.bind_opt uu____1905
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Refine (b1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1914)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1939 = unembed_const c  in
             FStar_Util.bind_opt uu____1939
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1948)::(t1,uu____1950)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1985 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1985
               (fun u1  ->
                  let uu____1991 = unembed_term t1  in
                  FStar_Util.bind_opt uu____1991
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_56  -> FStar_Pervasives_Native.Some _0_56)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____2000)::(b,uu____2002)::(t1,uu____2004)::(t2,uu____2006)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____2061 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____2061
               (fun r1  ->
                  let uu____2067 = unembed_bv b  in
                  FStar_Util.bind_opt uu____2067
                    (fun b1  ->
                       let uu____2073 = unembed_term t1  in
                       FStar_Util.bind_opt uu____2073
                         (fun t11  ->
                            let uu____2079 = unembed_term t2  in
                            FStar_Util.bind_opt uu____2079
                              (fun t21  ->
                                 FStar_All.pipe_left
                                   (fun _0_57  ->
                                      FStar_Pervasives_Native.Some _0_57)
                                   (FStar_Reflection_Data.Tv_Let
                                      (r1, b1, t11, t21))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t1,uu____2088)::(brs,uu____2090)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____2125 = unembed_term t1  in
             FStar_Util.bind_opt uu____2125
               (fun t2  ->
                  let uu____2131 =
                    let uu____2140 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____2140 brs  in
                  FStar_Util.bind_opt uu____2131
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                         (FStar_Reflection_Data.Tv_Match (t2, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e,uu____2179)::(t1,uu____2181)::(tacopt,uu____2183)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
             ->
             let uu____2228 = unembed_term e  in
             FStar_Util.bind_opt uu____2228
               (fun e1  ->
                  let uu____2234 = unembed_term t1  in
                  FStar_Util.bind_opt uu____2234
                    (fun t2  ->
                       let uu____2240 =
                         let uu____2245 =
                           FStar_Syntax_Embeddings.unembed_option
                             unembed_term
                            in
                         uu____2245 tacopt  in
                       FStar_Util.bind_opt uu____2240
                         (fun tacopt1  ->
                            FStar_All.pipe_left
                              (fun _0_59  ->
                                 FStar_Pervasives_Native.Some _0_59)
                              (FStar_Reflection_Data.Tv_AscribedT
                                 (e1, t2, tacopt1)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e,uu____2264)::(c,uu____2266)::(tacopt,uu____2268)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
             ->
             let uu____2313 = unembed_term e  in
             FStar_Util.bind_opt uu____2313
               (fun e1  ->
                  let uu____2319 = unembed_comp c  in
                  FStar_Util.bind_opt uu____2319
                    (fun c1  ->
                       let uu____2325 =
                         let uu____2330 =
                           FStar_Syntax_Embeddings.unembed_option
                             unembed_term
                            in
                         uu____2330 tacopt  in
                       FStar_Util.bind_opt uu____2325
                         (fun tacopt1  ->
                            FStar_All.pipe_left
                              (fun _0_60  ->
                                 FStar_Pervasives_Native.Some _0_60)
                              (FStar_Reflection_Data.Tv_AscribedC
                                 (e1, c1, tacopt1)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
               FStar_Reflection_Data.Tv_Unknown
         | uu____2364 ->
             ((let uu____2378 =
                 let uu____2383 =
                   let uu____2384 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____2384
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2383)  in
               FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2378);
              FStar_Pervasives_Native.None))
  
let (unembed_bv_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.bv_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2395 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2395 with
    | (hd1,args) ->
        let uu____2434 =
          let uu____2447 =
            let uu____2448 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2448.FStar_Syntax_Syntax.n  in
          (uu____2447, args)  in
        (match uu____2434 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2463)::(idx,uu____2465)::(s,uu____2467)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2512 = FStar_Syntax_Embeddings.unembed_string nm  in
             FStar_Util.bind_opt uu____2512
               (fun nm1  ->
                  let uu____2518 = FStar_Syntax_Embeddings.unembed_int idx
                     in
                  FStar_Util.bind_opt uu____2518
                    (fun idx1  ->
                       let uu____2524 = unembed_term s  in
                       FStar_Util.bind_opt uu____2524
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_62  ->
                                 FStar_Pervasives_Native.Some _0_62)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2531 ->
             ((let uu____2545 =
                 let uu____2550 =
                   let uu____2551 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded bv_view: %s"
                     uu____2551
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2550)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2545);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2562 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2562 with
    | (hd1,args) ->
        let uu____2601 =
          let uu____2614 =
            let uu____2615 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2615.FStar_Syntax_Syntax.n  in
          (uu____2614, args)  in
        (match uu____2601 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2630)::(md,uu____2632)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2667 = unembed_term t2  in
             FStar_Util.bind_opt uu____2667
               (fun t3  ->
                  let uu____2673 =
                    let uu____2678 =
                      FStar_Syntax_Embeddings.unembed_option unembed_term  in
                    uu____2678 md  in
                  FStar_Util.bind_opt uu____2673
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_63  -> FStar_Pervasives_Native.Some _0_63)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2697)::(post,uu____2699)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2734 = unembed_term pre  in
             FStar_Util.bind_opt uu____2734
               (fun pre1  ->
                  let uu____2740 = unembed_term post  in
                  FStar_Util.bind_opt uu____2740
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_65  -> FStar_Pervasives_Native.Some _0_65)
               FStar_Reflection_Data.C_Unknown
         | uu____2764 ->
             ((let uu____2778 =
                 let uu____2783 =
                   let uu____2784 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2784
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2783)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2778);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2795 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2795 with
    | (hd1,args) ->
        let uu____2834 =
          let uu____2847 =
            let uu____2848 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2848.FStar_Syntax_Syntax.n  in
          (uu____2847, args)  in
        (match uu____2834 with
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
         | uu____2906 ->
             ((let uu____2920 =
                 let uu____2925 =
                   let uu____2926 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____2926
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2925)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2920);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____2936 =
      let uu____2937 = FStar_Syntax_Subst.compress t  in
      uu____2937.FStar_Syntax_Syntax.n  in
    match uu____2936 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____2943 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____2943
    | uu____2944 ->
        ((let uu____2946 =
            let uu____2951 =
              let uu____2952 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____2952  in
            (FStar_Errors.Warning_NotEmbedded, uu____2951)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2946);
         FStar_Pervasives_Native.None)
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2963 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2963 with
    | (hd1,args) ->
        let uu____3002 =
          let uu____3015 =
            let uu____3016 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3016.FStar_Syntax_Syntax.n  in
          (uu____3015, args)  in
        (match uu____3002 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3031)::(bs,uu____3033)::(t2,uu____3035)::(dcs,uu____3037)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3092 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3092
               (fun nm1  ->
                  let uu____3104 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____3104
                    (fun bs1  ->
                       let uu____3110 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3110
                         (fun t3  ->
                            let uu____3116 =
                              let uu____3123 =
                                let uu____3130 =
                                  FStar_Syntax_Embeddings.unembed_list
                                    FStar_Syntax_Embeddings.unembed_string
                                   in
                                FStar_Syntax_Embeddings.unembed_list
                                  uu____3130
                                 in
                              uu____3123 dcs  in
                            FStar_Util.bind_opt uu____3116
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_Pervasives_Native.Some _0_66)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____3163)::(fvar1,uu____3165)::(ty,uu____3167)::(t2,uu____3169)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____3224 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____3224
               (fun r1  ->
                  let uu____3230 = unembed_fv fvar1  in
                  FStar_Util.bind_opt uu____3230
                    (fun fvar2  ->
                       let uu____3236 = unembed_term ty  in
                       FStar_Util.bind_opt uu____3236
                         (fun ty1  ->
                            let uu____3242 = unembed_term t2  in
                            FStar_Util.bind_opt uu____3242
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_Pervasives_Native.Some _0_67)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____3264 ->
             ((let uu____3278 =
                 let uu____3283 =
                   let uu____3284 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____3284
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3283)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3278);
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
    let uu____3295 =
      let uu____3296 =
        let uu____3297 =
          let uu____3298 =
            let uu____3299 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____3302 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____3302 i.FStar_Syntax_Syntax.rng uu____3299  in
          FStar_Syntax_Syntax.as_arg uu____3298  in
        [uu____3297]  in
      FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv
        uu____3296
       in
    uu____3295 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 