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
                let uu____214 = embed_fv rng fv  in
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
      | FStar_Reflection_Data.C_Total (t,md) ->
          let uu____401 =
            let uu____402 =
              let uu____403 =
                let uu____404 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____404  in
              let uu____405 =
                let uu____408 =
                  let uu____409 =
                    let uu____410 =
                      FStar_Syntax_Embeddings.embed_option embed_term
                        FStar_Syntax_Syntax.t_term
                       in
                    uu____410 rng md  in
                  FStar_Syntax_Syntax.as_arg uu____409  in
                [uu____408]  in
              uu____403 :: uu____405  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____402
             in
          uu____401 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____425 =
            let uu____426 =
              let uu____427 =
                let uu____428 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____428  in
              let uu____429 =
                let uu____432 =
                  let uu____433 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____433  in
                [uu____432]  in
              uu____427 :: uu____429  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____426
             in
          uu____425 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___54_436 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___54_436.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___54_436.FStar_Syntax_Syntax.vars)
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
      let uu___55_447 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_447.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_447.FStar_Syntax_Syntax.vars)
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
          let uu____470 =
            let uu____471 =
              let uu____472 =
                let uu____473 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____473  in
              let uu____474 =
                let uu____477 =
                  let uu____478 = embed_fv rng fv  in
                  FStar_Syntax_Syntax.as_arg uu____478  in
                let uu____479 =
                  let uu____482 =
                    let uu____483 = embed_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____483  in
                  let uu____484 =
                    let uu____487 =
                      let uu____488 = embed_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____488  in
                    [uu____487]  in
                  uu____482 :: uu____484  in
                uu____477 :: uu____479  in
              uu____472 :: uu____474  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____471
             in
          uu____470 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
          let uu____493 =
            let uu____494 =
              let uu____495 =
                let uu____496 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____496  in
              let uu____497 =
                let uu____500 =
                  let uu____501 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____501  in
                [uu____500]  in
              uu____495 :: uu____497  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
              uu____494
             in
          uu____493 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____516 =
            let uu____517 =
              let uu____518 =
                let uu____519 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____519  in
              let uu____520 =
                let uu____523 =
                  let uu____524 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____524  in
                let uu____525 =
                  let uu____528 =
                    let uu____529 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____529  in
                  let uu____530 =
                    let uu____533 =
                      let uu____534 =
                        let uu____535 =
                          let uu____542 =
                            FStar_Syntax_Syntax.t_list_of
                              FStar_Syntax_Syntax.t_string
                             in
                          FStar_Syntax_Embeddings.embed_list
                            FStar_Syntax_Embeddings.embed_string_list
                            uu____542
                           in
                        uu____535 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____534  in
                    [uu____533]  in
                  uu____528 :: uu____530  in
                uu____523 :: uu____525  in
              uu____518 :: uu____520  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____517
             in
          uu____516 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___56_550 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___56_550.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___56_550.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_bv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____560 =
      let uu____561 = FStar_Syntax_Subst.compress t  in
      uu____561.FStar_Syntax_Syntax.n  in
    match uu____560 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____567 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____567
    | uu____568 ->
        ((let uu____570 =
            let uu____575 =
              let uu____576 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____576  in
            (FStar_Errors.Warning_NotEmbedded, uu____575)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____570);
         FStar_Pervasives_Native.None)
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____586 =
      let uu____587 = FStar_Syntax_Subst.compress t  in
      uu____587.FStar_Syntax_Syntax.n  in
    match uu____586 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____593 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____593
    | uu____594 ->
        ((let uu____596 =
            let uu____601 =
              let uu____602 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____602  in
            (FStar_Errors.Warning_NotEmbedded, uu____601)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____596);
         FStar_Pervasives_Native.None)
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____613;
           FStar_Syntax_Syntax.pos = uu____614;
           FStar_Syntax_Syntax.vars = uu____615;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> FStar_Pervasives_Native.Some qt
    | uu____628 ->
        ((let uu____630 =
            let uu____635 =
              let uu____636 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____636  in
            (FStar_Errors.Warning_NotEmbedded, uu____635)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____630);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____647 = FStar_Syntax_Util.head_and_args t1  in
    match uu____647 with
    | (hd1,args) ->
        let uu____686 =
          let uu____699 =
            let uu____700 = FStar_Syntax_Util.un_uinst hd1  in
            uu____700.FStar_Syntax_Syntax.n  in
          (uu____699, args)  in
        (match uu____686 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____743 ->
             ((let uu____757 =
                 let uu____762 =
                   let uu____763 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____763
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____762)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____757);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____771 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____771 t
  
let (unembed_fv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____787 =
      let uu____788 = FStar_Syntax_Subst.compress t  in
      uu____788.FStar_Syntax_Syntax.n  in
    match uu____787 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____794 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____794
    | uu____795 ->
        ((let uu____797 =
            let uu____802 =
              let uu____803 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____803  in
            (FStar_Errors.Warning_NotEmbedded, uu____802)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____797);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____813 =
      let uu____814 = FStar_Syntax_Subst.compress t  in
      uu____814.FStar_Syntax_Syntax.n  in
    match uu____813 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____820 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____820
    | uu____821 ->
        ((let uu____823 =
            let uu____828 =
              let uu____829 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____829  in
            (FStar_Errors.Warning_NotEmbedded, uu____828)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____823);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____839 =
      let uu____840 = FStar_Syntax_Subst.compress t  in
      uu____840.FStar_Syntax_Syntax.n  in
    match uu____839 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____846 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____846
    | uu____847 ->
        ((let uu____849 =
            let uu____854 =
              let uu____855 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____855  in
            (FStar_Errors.Warning_NotEmbedded, uu____854)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____849);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____866 = FStar_Syntax_Util.head_and_args t1  in
    match uu____866 with
    | (hd1,args) ->
        let uu____905 =
          let uu____918 =
            let uu____919 = FStar_Syntax_Util.un_uinst hd1  in
            uu____919.FStar_Syntax_Syntax.n  in
          (uu____918, args)  in
        (match uu____905 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____979)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1004 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____1004
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1013)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1038 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____1038
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1045 ->
             ((let uu____1059 =
                 let uu____1064 =
                   let uu____1065 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____1065
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1064)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1059);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1074 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1074 with
    | (hd1,args) ->
        let uu____1113 =
          let uu____1126 =
            let uu____1127 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1127.FStar_Syntax_Syntax.n  in
          (uu____1126, args)  in
        (match uu____1113 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1142)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1167 = unembed_const c  in
             FStar_Util.bind_opt uu____1167
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1176)::(ps,uu____1178)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1213 = unembed_fv f  in
             FStar_Util.bind_opt uu____1213
               (fun f1  ->
                  let uu____1219 =
                    let uu____1224 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1224 ps  in
                  FStar_Util.bind_opt uu____1219
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1243)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1268 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1268
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var bv1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1277)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1302 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1302
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild bv1))
         | uu____1309 ->
             ((let uu____1323 =
                 let uu____1328 =
                   let uu____1329 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1329
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1328)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1323);
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
    let uu____1360 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1360 with
    | (hd1,args) ->
        let uu____1399 =
          let uu____1412 =
            let uu____1413 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1413.FStar_Syntax_Syntax.n  in
          (uu____1412, args)  in
        (match uu____1399 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1428)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1453 = unembed_bv b  in
             FStar_Util.bind_opt uu____1453
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1462)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
             ->
             let uu____1487 = unembed_bv b  in
             FStar_Util.bind_opt uu____1487
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_BVar b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1496)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1521 = unembed_fv f  in
             FStar_Util.bind_opt uu____1521
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1530)::(r,uu____1532)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1567 = unembed_term l  in
             FStar_Util.bind_opt uu____1567
               (fun l1  ->
                  let uu____1573 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1573
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1598)::(t2,uu____1600)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1635 = unembed_binder b  in
             FStar_Util.bind_opt uu____1635
               (fun b1  ->
                  let uu____1641 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1641
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1650)::(t2,uu____1652)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1687 = unembed_binder b  in
             FStar_Util.bind_opt uu____1687
               (fun b1  ->
                  let uu____1693 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1693
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1702)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1727 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1727
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1736)::(t2,uu____1738)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1773 = unembed_bv b  in
             FStar_Util.bind_opt uu____1773
               (fun b1  ->
                  let uu____1779 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1779
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1788)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1813 = unembed_const c  in
             FStar_Util.bind_opt uu____1813
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1822)::(t2,uu____1824)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1859 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1859
               (fun u1  ->
                  let uu____1865 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1865
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____1874)::(b,uu____1876)::(t11,uu____1878)::(t2,uu____1880)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____1935 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____1935
               (fun r1  ->
                  let uu____1941 = unembed_bv b  in
                  FStar_Util.bind_opt uu____1941
                    (fun b1  ->
                       let uu____1947 = unembed_term t11  in
                       FStar_Util.bind_opt uu____1947
                         (fun t12  ->
                            let uu____1953 = unembed_term t2  in
                            FStar_Util.bind_opt uu____1953
                              (fun t21  ->
                                 FStar_All.pipe_left
                                   (fun _0_56  ->
                                      FStar_Pervasives_Native.Some _0_56)
                                   (FStar_Reflection_Data.Tv_Let
                                      (r1, b1, t12, t21))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1962)::(brs,uu____1964)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____1999 = unembed_term t2  in
             FStar_Util.bind_opt uu____1999
               (fun t3  ->
                  let uu____2005 =
                    let uu____2014 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____2014 brs  in
                  FStar_Util.bind_opt uu____2005
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
         | uu____2068 ->
             ((let uu____2082 =
                 let uu____2087 =
                   let uu____2088 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____2088
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2087)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2082);
              FStar_Pervasives_Native.None))
  
let (unembed_bv_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.bv_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2099 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2099 with
    | (hd1,args) ->
        let uu____2138 =
          let uu____2151 =
            let uu____2152 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2152.FStar_Syntax_Syntax.n  in
          (uu____2151, args)  in
        (match uu____2138 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2167)::(idx,uu____2169)::(s,uu____2171)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2216 = FStar_Syntax_Embeddings.unembed_string nm  in
             FStar_Util.bind_opt uu____2216
               (fun nm1  ->
                  let uu____2222 = FStar_Syntax_Embeddings.unembed_int idx
                     in
                  FStar_Util.bind_opt uu____2222
                    (fun idx1  ->
                       let uu____2228 = unembed_term s  in
                       FStar_Util.bind_opt uu____2228
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_59  ->
                                 FStar_Pervasives_Native.Some _0_59)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2235 ->
             ((let uu____2249 =
                 let uu____2254 =
                   let uu____2255 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded bv_view: %s"
                     uu____2255
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2254)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2249);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2266 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2266 with
    | (hd1,args) ->
        let uu____2305 =
          let uu____2318 =
            let uu____2319 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2319.FStar_Syntax_Syntax.n  in
          (uu____2318, args)  in
        (match uu____2305 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2334)::(md,uu____2336)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2371 = unembed_term t2  in
             FStar_Util.bind_opt uu____2371
               (fun t3  ->
                  let uu____2377 =
                    let uu____2382 =
                      FStar_Syntax_Embeddings.unembed_option unembed_term  in
                    uu____2382 md  in
                  FStar_Util.bind_opt uu____2377
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_60  -> FStar_Pervasives_Native.Some _0_60)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2401)::(post,uu____2403)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2438 = unembed_term pre  in
             FStar_Util.bind_opt uu____2438
               (fun pre1  ->
                  let uu____2444 = unembed_term post  in
                  FStar_Util.bind_opt uu____2444
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
         | uu____2468 ->
             ((let uu____2482 =
                 let uu____2487 =
                   let uu____2488 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2488
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2487)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2482);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2499 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2499 with
    | (hd1,args) ->
        let uu____2538 =
          let uu____2551 =
            let uu____2552 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2552.FStar_Syntax_Syntax.n  in
          (uu____2551, args)  in
        (match uu____2538 with
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
         | uu____2610 ->
             ((let uu____2624 =
                 let uu____2629 =
                   let uu____2630 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____2630
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2629)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2624);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____2640 =
      let uu____2641 = FStar_Syntax_Subst.compress t  in
      uu____2641.FStar_Syntax_Syntax.n  in
    match uu____2640 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____2647 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____2647
    | uu____2648 ->
        ((let uu____2650 =
            let uu____2655 =
              let uu____2656 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____2656  in
            (FStar_Errors.Warning_NotEmbedded, uu____2655)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2650);
         FStar_Pervasives_Native.None)
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2667 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2667 with
    | (hd1,args) ->
        let uu____2706 =
          let uu____2719 =
            let uu____2720 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2720.FStar_Syntax_Syntax.n  in
          (uu____2719, args)  in
        (match uu____2706 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2735)::(bs,uu____2737)::(t2,uu____2739)::(dcs,uu____2741)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____2796 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____2796
               (fun nm1  ->
                  let uu____2808 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____2808
                    (fun bs1  ->
                       let uu____2814 = unembed_term t2  in
                       FStar_Util.bind_opt uu____2814
                         (fun t3  ->
                            let uu____2820 =
                              let uu____2827 =
                                let uu____2834 =
                                  FStar_Syntax_Embeddings.unembed_list
                                    FStar_Syntax_Embeddings.unembed_string
                                   in
                                FStar_Syntax_Embeddings.unembed_list
                                  uu____2834
                                 in
                              uu____2827 dcs  in
                            FStar_Util.bind_opt uu____2820
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_Pervasives_Native.Some _0_63)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____2867)::(fvar1,uu____2869)::(ty,uu____2871)::(t2,uu____2873)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____2928 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____2928
               (fun r1  ->
                  let uu____2934 = unembed_fv fvar1  in
                  FStar_Util.bind_opt uu____2934
                    (fun fvar2  ->
                       let uu____2940 = unembed_term ty  in
                       FStar_Util.bind_opt uu____2940
                         (fun ty1  ->
                            let uu____2946 = unembed_term t2  in
                            FStar_Util.bind_opt uu____2946
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
         | uu____2968 ->
             ((let uu____2982 =
                 let uu____2987 =
                   let uu____2988 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____2988
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2987)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2982);
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
    let uu____2999 =
      let uu____3000 =
        let uu____3001 =
          let uu____3002 =
            let uu____3003 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____3006 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____3006 i.FStar_Syntax_Syntax.rng uu____3003  in
          FStar_Syntax_Syntax.as_arg uu____3002  in
        [uu____3001]  in
      FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv
        uu____3000
       in
    uu____2999 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 