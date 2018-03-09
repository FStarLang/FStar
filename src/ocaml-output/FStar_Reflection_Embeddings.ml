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
  
let (embed_branch :
  FStar_Range.range ->
    FStar_Reflection_Data.branch -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun br  ->
      let uu____172 =
        FStar_Syntax_Embeddings.embed_pair embed_pattern
          FStar_Reflection_Data.fstar_refl_pattern embed_term
          FStar_Syntax_Syntax.t_term
         in
      uu____172 rng br
  
let (embed_argv :
  FStar_Range.range -> FStar_Reflection_Data.argv -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun aq  ->
      let uu____191 =
        FStar_Syntax_Embeddings.embed_pair embed_term
          FStar_Syntax_Syntax.t_term embed_aqualv
          FStar_Reflection_Data.fstar_refl_aqualv
         in
      uu____191 rng aq
  
let (embed_term_view :
  FStar_Range.range ->
    FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  ->
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____211 =
            let uu____212 =
              let uu____213 =
                let uu____214 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____214  in
              [uu____213]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____212
             in
          uu____211 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____218 =
            let uu____219 =
              let uu____220 =
                let uu____221 = embed_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____221  in
              [uu____220]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____219
             in
          uu____218 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____225 =
            let uu____226 =
              let uu____227 =
                let uu____228 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____228  in
              [uu____227]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____226
             in
          uu____225 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____233 =
            let uu____234 =
              let uu____235 =
                let uu____236 = embed_term rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____236  in
              let uu____237 =
                let uu____240 =
                  let uu____241 = embed_argv rng a  in
                  FStar_Syntax_Syntax.as_arg uu____241  in
                [uu____240]  in
              uu____235 :: uu____237  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____234
             in
          uu____233 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____246 =
            let uu____247 =
              let uu____248 =
                let uu____249 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____249  in
              let uu____250 =
                let uu____253 =
                  let uu____254 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____254  in
                [uu____253]  in
              uu____248 :: uu____250  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____247
             in
          uu____246 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____259 =
            let uu____260 =
              let uu____261 =
                let uu____262 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____262  in
              let uu____263 =
                let uu____266 =
                  let uu____267 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____267  in
                [uu____266]  in
              uu____261 :: uu____263  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____260
             in
          uu____259 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____271 =
            let uu____272 =
              let uu____273 =
                let uu____274 = FStar_Syntax_Embeddings.embed_unit rng ()  in
                FStar_Syntax_Syntax.as_arg uu____274  in
              [uu____273]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____272
             in
          uu____271 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____279 =
            let uu____280 =
              let uu____281 =
                let uu____282 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____282  in
              let uu____283 =
                let uu____286 =
                  let uu____287 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____287  in
                [uu____286]  in
              uu____281 :: uu____283  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____280
             in
          uu____279 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____291 =
            let uu____292 =
              let uu____293 =
                let uu____294 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____294  in
              [uu____293]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____292
             in
          uu____291 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____299 =
            let uu____300 =
              let uu____301 =
                let uu____302 = FStar_Syntax_Embeddings.embed_int rng u  in
                FStar_Syntax_Syntax.as_arg uu____302  in
              let uu____303 =
                let uu____306 =
                  let uu____307 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____307  in
                [uu____306]  in
              uu____301 :: uu____303  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____300
             in
          uu____299 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____314 =
            let uu____315 =
              let uu____316 =
                let uu____317 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____317  in
              let uu____318 =
                let uu____321 =
                  let uu____322 = embed_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____322  in
                let uu____323 =
                  let uu____326 =
                    let uu____327 = embed_term rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____327  in
                  let uu____328 =
                    let uu____331 =
                      let uu____332 = embed_term rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____332  in
                    [uu____331]  in
                  uu____326 :: uu____328  in
                uu____321 :: uu____323  in
              uu____316 :: uu____318  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____315
             in
          uu____314 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____341 =
            let uu____342 =
              let uu____343 =
                let uu____344 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____344  in
              let uu____345 =
                let uu____348 =
                  let uu____349 =
                    let uu____350 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____350 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____349  in
                [uu____348]  in
              uu____343 :: uu____345  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____342
             in
          uu____341 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___53_360 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___53_360.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___53_360.FStar_Syntax_Syntax.vars)
          }
  
let (embed_bv_view :
  FStar_Range.range ->
    FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun bvv  ->
      let uu____370 =
        let uu____371 =
          let uu____372 =
            let uu____373 =
              FStar_Syntax_Embeddings.embed_string rng
                bvv.FStar_Reflection_Data.bv_ppname
               in
            FStar_Syntax_Syntax.as_arg uu____373  in
          let uu____374 =
            let uu____377 =
              let uu____378 =
                FStar_Syntax_Embeddings.embed_int rng
                  bvv.FStar_Reflection_Data.bv_index
                 in
              FStar_Syntax_Syntax.as_arg uu____378  in
            let uu____379 =
              let uu____382 =
                let uu____383 =
                  embed_term rng bvv.FStar_Reflection_Data.bv_sort  in
                FStar_Syntax_Syntax.as_arg uu____383  in
              [uu____382]  in
            uu____377 :: uu____379  in
          uu____372 :: uu____374  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____371
         in
      uu____370 FStar_Pervasives_Native.None rng
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____396 =
            let uu____397 =
              let uu____398 =
                let uu____399 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____399  in
              [uu____398]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____397
             in
          uu____396 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____407 =
            let uu____408 =
              let uu____409 =
                let uu____410 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____410  in
              let uu____411 =
                let uu____414 =
                  let uu____415 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____415  in
                [uu____414]  in
              uu____409 :: uu____411  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____408
             in
          uu____407 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___54_418 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___54_418.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___54_418.FStar_Syntax_Syntax.vars)
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
      let uu___55_429 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_429.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_429.FStar_Syntax_Syntax.vars)
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
          let uu____452 =
            let uu____453 =
              let uu____454 =
                let uu____455 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____455  in
              let uu____456 =
                let uu____459 =
                  let uu____460 = embed_fvar rng fv  in
                  FStar_Syntax_Syntax.as_arg uu____460  in
                let uu____461 =
                  let uu____464 =
                    let uu____465 = embed_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____465  in
                  let uu____466 =
                    let uu____469 =
                      let uu____470 = embed_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____470  in
                    [uu____469]  in
                  uu____464 :: uu____466  in
                uu____459 :: uu____461  in
              uu____454 :: uu____456  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____453
             in
          uu____452 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
          let uu____475 =
            let uu____476 =
              let uu____477 =
                let uu____478 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____478  in
              let uu____479 =
                let uu____482 =
                  let uu____483 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____483  in
                [uu____482]  in
              uu____477 :: uu____479  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
              uu____476
             in
          uu____475 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____498 =
            let uu____499 =
              let uu____500 =
                let uu____501 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____501  in
              let uu____502 =
                let uu____505 =
                  let uu____506 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____506  in
                let uu____507 =
                  let uu____510 =
                    let uu____511 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____511  in
                  let uu____512 =
                    let uu____515 =
                      let uu____516 =
                        let uu____517 =
                          let uu____524 =
                            FStar_Syntax_Syntax.t_list_of
                              FStar_Syntax_Syntax.t_string
                             in
                          FStar_Syntax_Embeddings.embed_list
                            FStar_Syntax_Embeddings.embed_string_list
                            uu____524
                           in
                        uu____517 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____516  in
                    [uu____515]  in
                  uu____510 :: uu____512  in
                uu____505 :: uu____507  in
              uu____500 :: uu____502  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____499
             in
          uu____498 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___56_532 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___56_532.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___56_532.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_bv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____542 =
      let uu____543 = FStar_Syntax_Subst.compress t  in
      uu____543.FStar_Syntax_Syntax.n  in
    match uu____542 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____549 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____549
    | uu____550 ->
        ((let uu____552 =
            let uu____557 =
              let uu____558 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____558  in
            (FStar_Errors.Warning_NotEmbedded, uu____557)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____552);
         FStar_Pervasives_Native.None)
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____568 =
      let uu____569 = FStar_Syntax_Subst.compress t  in
      uu____569.FStar_Syntax_Syntax.n  in
    match uu____568 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____575 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____575
    | uu____576 ->
        ((let uu____578 =
            let uu____583 =
              let uu____584 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____584  in
            (FStar_Errors.Warning_NotEmbedded, uu____583)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____578);
         FStar_Pervasives_Native.None)
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____595;
           FStar_Syntax_Syntax.pos = uu____596;
           FStar_Syntax_Syntax.vars = uu____597;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> FStar_Pervasives_Native.Some qt
    | uu____610 ->
        ((let uu____612 =
            let uu____617 =
              let uu____618 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____618  in
            (FStar_Errors.Warning_NotEmbedded, uu____617)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____612);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____629 = FStar_Syntax_Util.head_and_args t1  in
    match uu____629 with
    | (hd1,args) ->
        let uu____668 =
          let uu____681 =
            let uu____682 = FStar_Syntax_Util.un_uinst hd1  in
            uu____682.FStar_Syntax_Syntax.n  in
          (uu____681, args)  in
        (match uu____668 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____725 ->
             ((let uu____739 =
                 let uu____744 =
                   let uu____745 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____745
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____744)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____739);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____753 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____753 t
  
let (unembed_fvar :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____769 =
      let uu____770 = FStar_Syntax_Subst.compress t  in
      uu____770.FStar_Syntax_Syntax.n  in
    match uu____769 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____776 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____776
    | uu____777 ->
        ((let uu____779 =
            let uu____784 =
              let uu____785 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____785  in
            (FStar_Errors.Warning_NotEmbedded, uu____784)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____779);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____795 =
      let uu____796 = FStar_Syntax_Subst.compress t  in
      uu____796.FStar_Syntax_Syntax.n  in
    match uu____795 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____802 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____802
    | uu____803 ->
        ((let uu____805 =
            let uu____810 =
              let uu____811 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____811  in
            (FStar_Errors.Warning_NotEmbedded, uu____810)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____805);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____821 =
      let uu____822 = FStar_Syntax_Subst.compress t  in
      uu____822.FStar_Syntax_Syntax.n  in
    match uu____821 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____828 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____828
    | uu____829 ->
        ((let uu____831 =
            let uu____836 =
              let uu____837 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____837  in
            (FStar_Errors.Warning_NotEmbedded, uu____836)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____831);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____848 = FStar_Syntax_Util.head_and_args t1  in
    match uu____848 with
    | (hd1,args) ->
        let uu____887 =
          let uu____900 =
            let uu____901 = FStar_Syntax_Util.un_uinst hd1  in
            uu____901.FStar_Syntax_Syntax.n  in
          (uu____900, args)  in
        (match uu____887 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____961)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____986 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____986
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____995)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1020 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____1020
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1027 ->
             ((let uu____1041 =
                 let uu____1046 =
                   let uu____1047 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____1047
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1046)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1041);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1056 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1056 with
    | (hd1,args) ->
        let uu____1095 =
          let uu____1108 =
            let uu____1109 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1109.FStar_Syntax_Syntax.n  in
          (uu____1108, args)  in
        (match uu____1095 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1124)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1149 = unembed_const c  in
             FStar_Util.bind_opt uu____1149
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1158)::(ps,uu____1160)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1195 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1195
               (fun f1  ->
                  let uu____1201 =
                    let uu____1206 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1206 ps  in
                  FStar_Util.bind_opt uu____1201
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1225)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1250 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1250
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var bv1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1259)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1284 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1284
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild bv1))
         | uu____1291 ->
             ((let uu____1305 =
                 let uu____1310 =
                   let uu____1311 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1311
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1310)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1305);
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
    let uu____1342 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1342 with
    | (hd1,args) ->
        let uu____1381 =
          let uu____1394 =
            let uu____1395 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1395.FStar_Syntax_Syntax.n  in
          (uu____1394, args)  in
        (match uu____1381 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1410)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1435 = unembed_bv b  in
             FStar_Util.bind_opt uu____1435
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1444)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
             ->
             let uu____1469 = unembed_bv b  in
             FStar_Util.bind_opt uu____1469
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_BVar b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1478)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1503 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1503
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1512)::(r,uu____1514)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1549 = unembed_term l  in
             FStar_Util.bind_opt uu____1549
               (fun l1  ->
                  let uu____1555 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1555
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1580)::(t2,uu____1582)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1617 = unembed_binder b  in
             FStar_Util.bind_opt uu____1617
               (fun b1  ->
                  let uu____1623 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1623
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1632)::(t2,uu____1634)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1669 = unembed_binder b  in
             FStar_Util.bind_opt uu____1669
               (fun b1  ->
                  let uu____1675 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1675
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1684)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1709 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1709
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1718)::(t2,uu____1720)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1755 = unembed_bv b  in
             FStar_Util.bind_opt uu____1755
               (fun b1  ->
                  let uu____1761 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1761
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1770)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1795 = unembed_const c  in
             FStar_Util.bind_opt uu____1795
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1804)::(t2,uu____1806)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1841 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1841
               (fun u1  ->
                  let uu____1847 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1847
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____1856)::(b,uu____1858)::(t11,uu____1860)::(t2,uu____1862)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____1917 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____1917
               (fun r1  ->
                  let uu____1923 = unembed_bv b  in
                  FStar_Util.bind_opt uu____1923
                    (fun b1  ->
                       let uu____1929 = unembed_term t11  in
                       FStar_Util.bind_opt uu____1929
                         (fun t12  ->
                            let uu____1935 = unembed_term t2  in
                            FStar_Util.bind_opt uu____1935
                              (fun t21  ->
                                 FStar_All.pipe_left
                                   (fun _0_56  ->
                                      FStar_Pervasives_Native.Some _0_56)
                                   (FStar_Reflection_Data.Tv_Let
                                      (r1, b1, t12, t21))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1944)::(brs,uu____1946)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____1981 = unembed_term t2  in
             FStar_Util.bind_opt uu____1981
               (fun t3  ->
                  let uu____1987 =
                    let uu____1996 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____1996 brs  in
                  FStar_Util.bind_opt uu____1987
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                         (FStar_Reflection_Data.Tv_Match (t3, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
               FStar_Reflection_Data.Tv_Unknown
         | uu____2050 ->
             ((let uu____2064 =
                 let uu____2069 =
                   let uu____2070 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____2070
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2069)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2064);
              FStar_Pervasives_Native.None))
  
let (unembed_bv_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.bv_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2081 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2081 with
    | (hd1,args) ->
        let uu____2120 =
          let uu____2133 =
            let uu____2134 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2134.FStar_Syntax_Syntax.n  in
          (uu____2133, args)  in
        (match uu____2120 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2149)::(idx,uu____2151)::(s,uu____2153)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2198 = FStar_Syntax_Embeddings.unembed_string nm  in
             FStar_Util.bind_opt uu____2198
               (fun nm1  ->
                  let uu____2204 = FStar_Syntax_Embeddings.unembed_int idx
                     in
                  FStar_Util.bind_opt uu____2204
                    (fun idx1  ->
                       let uu____2210 = unembed_term s  in
                       FStar_Util.bind_opt uu____2210
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_59  ->
                                 FStar_Pervasives_Native.Some _0_59)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2217 ->
             ((let uu____2231 =
                 let uu____2236 =
                   let uu____2237 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded bv_view: %s"
                     uu____2237
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2236)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2231);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2248 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2248 with
    | (hd1,args) ->
        let uu____2287 =
          let uu____2300 =
            let uu____2301 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2301.FStar_Syntax_Syntax.n  in
          (uu____2300, args)  in
        (match uu____2287 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____2316)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2341 = unembed_term t2  in
             FStar_Util.bind_opt uu____2341
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_60  -> FStar_Pervasives_Native.Some _0_60)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2350)::(post,uu____2352)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2387 = unembed_term pre  in
             FStar_Util.bind_opt uu____2387
               (fun pre1  ->
                  let uu____2393 = unembed_term post  in
                  FStar_Util.bind_opt uu____2393
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_62  -> FStar_Pervasives_Native.Some _0_62)
               FStar_Reflection_Data.C_Unknown
         | uu____2417 ->
             ((let uu____2431 =
                 let uu____2436 =
                   let uu____2437 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2437
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2436)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2431);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2448 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2448 with
    | (hd1,args) ->
        let uu____2487 =
          let uu____2500 =
            let uu____2501 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2501.FStar_Syntax_Syntax.n  in
          (uu____2500, args)  in
        (match uu____2487 with
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
         | uu____2559 ->
             ((let uu____2573 =
                 let uu____2578 =
                   let uu____2579 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____2579
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2578)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2573);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____2589 =
      let uu____2590 = FStar_Syntax_Subst.compress t  in
      uu____2590.FStar_Syntax_Syntax.n  in
    match uu____2589 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____2596 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____2596
    | uu____2597 ->
        ((let uu____2599 =
            let uu____2604 =
              let uu____2605 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____2605  in
            (FStar_Errors.Warning_NotEmbedded, uu____2604)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2599);
         FStar_Pervasives_Native.None)
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2616 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2616 with
    | (hd1,args) ->
        let uu____2655 =
          let uu____2668 =
            let uu____2669 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2669.FStar_Syntax_Syntax.n  in
          (uu____2668, args)  in
        (match uu____2655 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2684)::(bs,uu____2686)::(t2,uu____2688)::(dcs,uu____2690)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____2745 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____2745
               (fun nm1  ->
                  let uu____2757 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____2757
                    (fun bs1  ->
                       let uu____2763 = unembed_term t2  in
                       FStar_Util.bind_opt uu____2763
                         (fun t3  ->
                            let uu____2769 =
                              let uu____2776 =
                                let uu____2783 =
                                  FStar_Syntax_Embeddings.unembed_list
                                    FStar_Syntax_Embeddings.unembed_string
                                   in
                                FStar_Syntax_Embeddings.unembed_list
                                  uu____2783
                                 in
                              uu____2776 dcs  in
                            FStar_Util.bind_opt uu____2769
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_Pervasives_Native.Some _0_63)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____2816)::(fvar1,uu____2818)::(ty,uu____2820)::(t2,uu____2822)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____2877 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____2877
               (fun r1  ->
                  let uu____2883 = unembed_fvar fvar1  in
                  FStar_Util.bind_opt uu____2883
                    (fun fvar2  ->
                       let uu____2889 = unembed_term ty  in
                       FStar_Util.bind_opt uu____2889
                         (fun ty1  ->
                            let uu____2895 = unembed_term t2  in
                            FStar_Util.bind_opt uu____2895
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_Pervasives_Native.Some _0_64)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____2917 ->
             ((let uu____2931 =
                 let uu____2936 =
                   let uu____2937 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____2937
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2936)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2931);
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
    let uu____2948 =
      let uu____2949 =
        let uu____2950 =
          let uu____2951 =
            let uu____2952 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____2955 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____2955 i.FStar_Syntax_Syntax.rng uu____2952  in
          FStar_Syntax_Syntax.as_arg uu____2951  in
        [uu____2950]  in
      FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv
        uu____2949
       in
    uu____2948 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 