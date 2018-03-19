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
      let qi =
        { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static }  in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (t, qi))
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
  
let rec (embed_exp :
  FStar_Reflection_Data.exp FStar_Syntax_Embeddings.embedder) =
  fun rng  ->
    fun e  ->
      let r =
        match e with
        | FStar_Reflection_Data.Unit  ->
            FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.t
        | FStar_Reflection_Data.Var i ->
            let uu____635 =
              let uu____636 =
                let uu____637 =
                  let uu____638 =
                    let uu____639 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____639  in
                  FStar_Syntax_Syntax.as_arg uu____638  in
                [uu____637]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
                uu____636
               in
            uu____635 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.Mult (e1,e2) ->
            let uu____644 =
              let uu____645 =
                let uu____646 =
                  let uu____647 = embed_exp rng e1  in
                  FStar_Syntax_Syntax.as_arg uu____647  in
                let uu____648 =
                  let uu____651 =
                    let uu____652 = embed_exp rng e2  in
                    FStar_Syntax_Syntax.as_arg uu____652  in
                  [uu____651]  in
                uu____646 :: uu____648  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
                uu____645
               in
            uu____644 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___57_655 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___57_655.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___57_655.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_bv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____665 =
      let uu____666 = FStar_Syntax_Subst.compress t  in
      uu____666.FStar_Syntax_Syntax.n  in
    match uu____665 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____672 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____672
    | uu____673 ->
        ((let uu____675 =
            let uu____680 =
              let uu____681 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____681  in
            (FStar_Errors.Warning_NotEmbedded, uu____680)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____675);
         FStar_Pervasives_Native.None)
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____691 =
      let uu____692 = FStar_Syntax_Subst.compress t  in
      uu____692.FStar_Syntax_Syntax.n  in
    match uu____691 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____698 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____698
    | uu____699 ->
        ((let uu____701 =
            let uu____706 =
              let uu____707 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____707  in
            (FStar_Errors.Warning_NotEmbedded, uu____706)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____701);
         FStar_Pervasives_Native.None)
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        FStar_Pervasives_Native.Some tm
    | uu____726 ->
        ((let uu____728 =
            let uu____733 =
              let uu____734 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____734  in
            (FStar_Errors.Warning_NotEmbedded, uu____733)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____728);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____745 = FStar_Syntax_Util.head_and_args t1  in
    match uu____745 with
    | (hd1,args) ->
        let uu____784 =
          let uu____797 =
            let uu____798 = FStar_Syntax_Util.un_uinst hd1  in
            uu____798.FStar_Syntax_Syntax.n  in
          (uu____797, args)  in
        (match uu____784 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____841 ->
             ((let uu____855 =
                 let uu____860 =
                   let uu____861 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____861
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____860)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____855);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____869 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____869 t
  
let (unembed_fv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____885 =
      let uu____886 = FStar_Syntax_Subst.compress t  in
      uu____886.FStar_Syntax_Syntax.n  in
    match uu____885 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____892 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____892
    | uu____893 ->
        ((let uu____895 =
            let uu____900 =
              let uu____901 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____901  in
            (FStar_Errors.Warning_NotEmbedded, uu____900)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____895);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____911 =
      let uu____912 = FStar_Syntax_Subst.compress t  in
      uu____912.FStar_Syntax_Syntax.n  in
    match uu____911 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____918 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____918
    | uu____919 ->
        ((let uu____921 =
            let uu____926 =
              let uu____927 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____927  in
            (FStar_Errors.Warning_NotEmbedded, uu____926)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____921);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____937 =
      let uu____938 = FStar_Syntax_Subst.compress t  in
      uu____938.FStar_Syntax_Syntax.n  in
    match uu____937 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____944 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____944
    | uu____945 ->
        ((let uu____947 =
            let uu____952 =
              let uu____953 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____953  in
            (FStar_Errors.Warning_NotEmbedded, uu____952)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____947);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____964 = FStar_Syntax_Util.head_and_args t1  in
    match uu____964 with
    | (hd1,args) ->
        let uu____1003 =
          let uu____1016 =
            let uu____1017 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1017.FStar_Syntax_Syntax.n  in
          (uu____1016, args)  in
        (match uu____1003 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1077)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1102 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____1102
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1111)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1136 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____1136
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1143 ->
             ((let uu____1157 =
                 let uu____1162 =
                   let uu____1163 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____1163
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1162)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1157);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1172 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1172 with
    | (hd1,args) ->
        let uu____1211 =
          let uu____1224 =
            let uu____1225 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1225.FStar_Syntax_Syntax.n  in
          (uu____1224, args)  in
        (match uu____1211 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1240)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1265 = unembed_const c  in
             FStar_Util.bind_opt uu____1265
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1274)::(ps,uu____1276)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1311 = unembed_fv f  in
             FStar_Util.bind_opt uu____1311
               (fun f1  ->
                  let uu____1317 =
                    let uu____1322 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1322 ps  in
                  FStar_Util.bind_opt uu____1317
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1341)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1366 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1366
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var bv1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1375)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1400 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1400
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild bv1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(bv,uu____1409)::(t2,uu____1411)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
             ->
             let uu____1446 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1446
               (fun bv1  ->
                  let uu____1452 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1452
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                         (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
         | uu____1459 ->
             ((let uu____1473 =
                 let uu____1478 =
                   let uu____1479 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1479
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1478)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1473);
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
    let uu____1509 = FStar_Syntax_Util.head_and_args t  in
    match uu____1509 with
    | (hd1,args) ->
        let uu____1548 =
          let uu____1561 =
            let uu____1562 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1562.FStar_Syntax_Syntax.n  in
          (uu____1561, args)  in
        (match uu____1548 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1577)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1602 = unembed_bv b  in
             FStar_Util.bind_opt uu____1602
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1611)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
             ->
             let uu____1636 = unembed_bv b  in
             FStar_Util.bind_opt uu____1636
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                    (FStar_Reflection_Data.Tv_BVar b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1645)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1670 = unembed_fv f  in
             FStar_Util.bind_opt uu____1670
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1679)::(r,uu____1681)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1716 = unembed_term l  in
             FStar_Util.bind_opt uu____1716
               (fun l1  ->
                  let uu____1722 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1722
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1747)::(t1,uu____1749)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1784 = unembed_binder b  in
             FStar_Util.bind_opt uu____1784
               (fun b1  ->
                  let uu____1790 = unembed_term t1  in
                  FStar_Util.bind_opt uu____1790
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                         (FStar_Reflection_Data.Tv_Abs (b1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1799)::(t1,uu____1801)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1836 = unembed_binder b  in
             FStar_Util.bind_opt uu____1836
               (fun b1  ->
                  let uu____1842 = unembed_comp t1  in
                  FStar_Util.bind_opt uu____1842
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1851)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1876 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1876
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1885)::(t1,uu____1887)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1922 = unembed_bv b  in
             FStar_Util.bind_opt uu____1922
               (fun b1  ->
                  let uu____1928 = unembed_term t1  in
                  FStar_Util.bind_opt uu____1928
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Refine (b1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1937)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1962 = unembed_const c  in
             FStar_Util.bind_opt uu____1962
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1971)::(t1,uu____1973)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____2008 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____2008
               (fun u1  ->
                  let uu____2014 = unembed_term t1  in
                  FStar_Util.bind_opt uu____2014
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_56  -> FStar_Pervasives_Native.Some _0_56)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____2023)::(b,uu____2025)::(t1,uu____2027)::(t2,uu____2029)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____2084 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____2084
               (fun r1  ->
                  let uu____2090 = unembed_bv b  in
                  FStar_Util.bind_opt uu____2090
                    (fun b1  ->
                       let uu____2096 = unembed_term t1  in
                       FStar_Util.bind_opt uu____2096
                         (fun t11  ->
                            let uu____2102 = unembed_term t2  in
                            FStar_Util.bind_opt uu____2102
                              (fun t21  ->
                                 FStar_All.pipe_left
                                   (fun _0_57  ->
                                      FStar_Pervasives_Native.Some _0_57)
                                   (FStar_Reflection_Data.Tv_Let
                                      (r1, b1, t11, t21))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t1,uu____2111)::(brs,uu____2113)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____2148 = unembed_term t1  in
             FStar_Util.bind_opt uu____2148
               (fun t2  ->
                  let uu____2154 =
                    let uu____2163 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____2163 brs  in
                  FStar_Util.bind_opt uu____2154
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                         (FStar_Reflection_Data.Tv_Match (t2, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e,uu____2202)::(t1,uu____2204)::(tacopt,uu____2206)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
             ->
             let uu____2251 = unembed_term e  in
             FStar_Util.bind_opt uu____2251
               (fun e1  ->
                  let uu____2257 = unembed_term t1  in
                  FStar_Util.bind_opt uu____2257
                    (fun t2  ->
                       let uu____2263 =
                         let uu____2268 =
                           FStar_Syntax_Embeddings.unembed_option
                             unembed_term
                            in
                         uu____2268 tacopt  in
                       FStar_Util.bind_opt uu____2263
                         (fun tacopt1  ->
                            FStar_All.pipe_left
                              (fun _0_59  ->
                                 FStar_Pervasives_Native.Some _0_59)
                              (FStar_Reflection_Data.Tv_AscribedT
                                 (e1, t2, tacopt1)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e,uu____2287)::(c,uu____2289)::(tacopt,uu____2291)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
             ->
             let uu____2336 = unembed_term e  in
             FStar_Util.bind_opt uu____2336
               (fun e1  ->
                  let uu____2342 = unembed_comp c  in
                  FStar_Util.bind_opt uu____2342
                    (fun c1  ->
                       let uu____2348 =
                         let uu____2353 =
                           FStar_Syntax_Embeddings.unembed_option
                             unembed_term
                            in
                         uu____2353 tacopt  in
                       FStar_Util.bind_opt uu____2348
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
         | uu____2387 ->
             ((let uu____2401 =
                 let uu____2406 =
                   let uu____2407 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____2407
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2406)  in
               FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2401);
              FStar_Pervasives_Native.None))
  
let (unembed_bv_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.bv_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2418 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2418 with
    | (hd1,args) ->
        let uu____2457 =
          let uu____2470 =
            let uu____2471 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2471.FStar_Syntax_Syntax.n  in
          (uu____2470, args)  in
        (match uu____2457 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2486)::(idx,uu____2488)::(s,uu____2490)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2535 = FStar_Syntax_Embeddings.unembed_string nm  in
             FStar_Util.bind_opt uu____2535
               (fun nm1  ->
                  let uu____2541 = FStar_Syntax_Embeddings.unembed_int idx
                     in
                  FStar_Util.bind_opt uu____2541
                    (fun idx1  ->
                       let uu____2547 = unembed_term s  in
                       FStar_Util.bind_opt uu____2547
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_62  ->
                                 FStar_Pervasives_Native.Some _0_62)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2554 ->
             ((let uu____2568 =
                 let uu____2573 =
                   let uu____2574 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded bv_view: %s"
                     uu____2574
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2573)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2568);
              FStar_Pervasives_Native.None))
  
let rec (unembed_exp :
  FStar_Reflection_Data.exp FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2583 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2583 with
    | (hd1,args) ->
        let uu____2622 =
          let uu____2635 =
            let uu____2636 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2636.FStar_Syntax_Syntax.n  in
          (uu____2635, args)  in
        (match uu____2622 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____2666)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____2691 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____2691
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_63  -> FStar_Pervasives_Native.Some _0_63)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____2700)::(e2,uu____2702)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____2737 = unembed_exp e1  in
             FStar_Util.bind_opt uu____2737
               (fun e11  ->
                  let uu____2743 = unembed_exp e2  in
                  FStar_Util.bind_opt uu____2743
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____2750 ->
             ((let uu____2764 =
                 let uu____2769 =
                   let uu____2770 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded exp: %s" uu____2770
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2769)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2764);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2781 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2781 with
    | (hd1,args) ->
        let uu____2820 =
          let uu____2833 =
            let uu____2834 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2834.FStar_Syntax_Syntax.n  in
          (uu____2833, args)  in
        (match uu____2820 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2849)::(md,uu____2851)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2886 = unembed_term t2  in
             FStar_Util.bind_opt uu____2886
               (fun t3  ->
                  let uu____2892 =
                    let uu____2897 =
                      FStar_Syntax_Embeddings.unembed_option unembed_term  in
                    uu____2897 md  in
                  FStar_Util.bind_opt uu____2892
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_65  -> FStar_Pervasives_Native.Some _0_65)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2916)::(post,uu____2918)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2953 = unembed_term pre  in
             FStar_Util.bind_opt uu____2953
               (fun pre1  ->
                  let uu____2959 = unembed_term post  in
                  FStar_Util.bind_opt uu____2959
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_66  -> FStar_Pervasives_Native.Some _0_66)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_67  -> FStar_Pervasives_Native.Some _0_67)
               FStar_Reflection_Data.C_Unknown
         | uu____2983 ->
             ((let uu____2997 =
                 let uu____3002 =
                   let uu____3003 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____3003
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3002)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2997);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3014 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3014 with
    | (hd1,args) ->
        let uu____3053 =
          let uu____3066 =
            let uu____3067 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3067.FStar_Syntax_Syntax.n  in
          (uu____3066, args)  in
        (match uu____3053 with
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
         | uu____3125 ->
             ((let uu____3139 =
                 let uu____3144 =
                   let uu____3145 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____3145
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3144)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3139);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____3155 =
      let uu____3156 = FStar_Syntax_Subst.compress t  in
      uu____3156.FStar_Syntax_Syntax.n  in
    match uu____3155 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____3162 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____3162
    | uu____3163 ->
        ((let uu____3165 =
            let uu____3170 =
              let uu____3171 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3171  in
            (FStar_Errors.Warning_NotEmbedded, uu____3170)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____3165);
         FStar_Pervasives_Native.None)
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3182 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3182 with
    | (hd1,args) ->
        let uu____3221 =
          let uu____3234 =
            let uu____3235 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3235.FStar_Syntax_Syntax.n  in
          (uu____3234, args)  in
        (match uu____3221 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3250)::(bs,uu____3252)::(t2,uu____3254)::(dcs,uu____3256)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3311 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3311
               (fun nm1  ->
                  let uu____3323 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____3323
                    (fun bs1  ->
                       let uu____3329 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3329
                         (fun t3  ->
                            let uu____3335 =
                              let uu____3342 =
                                let uu____3349 =
                                  FStar_Syntax_Embeddings.unembed_list
                                    FStar_Syntax_Embeddings.unembed_string
                                   in
                                FStar_Syntax_Embeddings.unembed_list
                                  uu____3349
                                 in
                              uu____3342 dcs  in
                            FStar_Util.bind_opt uu____3335
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_Pervasives_Native.Some _0_68)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____3382)::(fvar1,uu____3384)::(ty,uu____3386)::(t2,uu____3388)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____3443 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____3443
               (fun r1  ->
                  let uu____3449 = unembed_fv fvar1  in
                  FStar_Util.bind_opt uu____3449
                    (fun fvar2  ->
                       let uu____3455 = unembed_term ty  in
                       FStar_Util.bind_opt uu____3455
                         (fun ty1  ->
                            let uu____3461 = unembed_term t2  in
                            FStar_Util.bind_opt uu____3461
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_Pervasives_Native.Some _0_69)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____3483 ->
             ((let uu____3497 =
                 let uu____3502 =
                   let uu____3503 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____3503
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3502)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3497);
              FStar_Pervasives_Native.None))
  
let (embed_binder_view :
  (FStar_Syntax_Syntax.bv,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedder)
  =
  FStar_Syntax_Embeddings.embed_pair embed_bv
    FStar_Reflection_Data.fstar_refl_bv_view embed_aqualv
    FStar_Reflection_Data.fstar_refl_aqualv
  
let (unembed_binder_view :
  (FStar_Syntax_Syntax.bv,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_pair unembed_bv unembed_aqualv 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3530 =
      let uu____3531 =
        let uu____3532 =
          let uu____3533 =
            let uu____3534 = FStar_Reflection_Basic.inspect_bv bv  in
            embed_bv_view i.FStar_Syntax_Syntax.rng uu____3534  in
          FStar_Syntax_Syntax.as_arg uu____3533  in
        [uu____3532]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____3531
       in
    uu____3530 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3541 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____3541 with
    | (bv,aq) ->
        let uu____3548 =
          let uu____3549 =
            let uu____3550 =
              let uu____3551 = embed_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____3551  in
            let uu____3552 =
              let uu____3555 =
                let uu____3556 = embed_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____3556  in
              [uu____3555]  in
            uu____3550 :: uu____3552  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____3549
           in
        uu____3548 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3563 =
      let uu____3564 =
        let uu____3565 =
          let uu____3566 =
            let uu____3567 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____3570 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____3570 i.FStar_Syntax_Syntax.rng uu____3567  in
          FStar_Syntax_Syntax.as_arg uu____3566  in
        [uu____3565]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____3564
       in
    uu____3563 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3584 =
      let uu____3585 =
        let uu____3586 =
          let uu____3587 =
            let uu____3588 = FStar_Reflection_Basic.inspect_comp comp  in
            embed_comp_view i.FStar_Syntax_Syntax.rng uu____3588  in
          FStar_Syntax_Syntax.as_arg uu____3587  in
        [uu____3586]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____3585
       in
    uu____3584 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3598 =
      let uu____3599 =
        let uu____3600 =
          let uu____3601 =
            let uu____3602 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed_sigelt_view i.FStar_Syntax_Syntax.rng uu____3602  in
          FStar_Syntax_Syntax.as_arg uu____3601  in
        [uu____3600]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____3599
       in
    uu____3598 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  