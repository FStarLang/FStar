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
        {
          FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
          FStar_Syntax_Syntax.antiquotes = []
        }  in
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
      let uu___51_47 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___51_47.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___51_47.FStar_Syntax_Syntax.vars)
      }
  
let (embed_binders :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun l  ->
      let uu____57 =
        FStar_Syntax_Embeddings.embed_list embed_binder
          FStar_Reflection_Data.fstar_refl_binder
         in
      uu____57 rng l
  
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
            let uu____103 =
              let uu____104 =
                let uu____105 =
                  let uu____106 =
                    let uu____107 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____107  in
                  FStar_Syntax_Syntax.as_arg uu____106  in
                [uu____105]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
                uu____104
               in
            uu____103 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____111 =
              let uu____112 =
                let uu____113 =
                  let uu____114 = FStar_Syntax_Embeddings.embed_string rng s
                     in
                  FStar_Syntax_Syntax.as_arg uu____114  in
                [uu____113]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
                uu____112
               in
            uu____111 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___52_117 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___52_117.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___52_117.FStar_Syntax_Syntax.vars)
      }
  
let rec (embed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedder) =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____126 =
            let uu____127 =
              let uu____128 =
                let uu____129 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____129  in
              [uu____128]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____127
             in
          uu____126 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____138 =
            let uu____139 =
              let uu____140 =
                let uu____141 = embed_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____141  in
              let uu____142 =
                let uu____145 =
                  let uu____146 =
                    let uu____147 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern
                       in
                    uu____147 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____146  in
                [uu____145]  in
              uu____140 :: uu____142  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____139
             in
          uu____138 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____158 =
            let uu____159 =
              let uu____160 =
                let uu____161 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____161  in
              [uu____160]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____159
             in
          uu____158 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____165 =
            let uu____166 =
              let uu____167 =
                let uu____168 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____168  in
              [uu____167]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____166
             in
          uu____165 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____173 =
            let uu____174 =
              let uu____175 =
                let uu____176 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____176  in
              let uu____177 =
                let uu____180 =
                  let uu____181 = embed_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____181  in
                [uu____180]  in
              uu____175 :: uu____177  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____174
             in
          uu____173 FStar_Pervasives_Native.None rng
  
let (embed_branch :
  FStar_Range.range ->
    FStar_Reflection_Data.branch -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun br  ->
      let uu____193 =
        FStar_Syntax_Embeddings.embed_tuple2 embed_pattern
          FStar_Reflection_Data.fstar_refl_pattern embed_term
          FStar_Syntax_Syntax.t_term
         in
      uu____193 rng br
  
let (embed_argv :
  FStar_Range.range -> FStar_Reflection_Data.argv -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun aq  ->
      let uu____212 =
        FStar_Syntax_Embeddings.embed_tuple2 embed_term
          FStar_Syntax_Syntax.t_term embed_aqualv
          FStar_Reflection_Data.fstar_refl_aqualv
         in
      uu____212 rng aq
  
let (embed_term_view :
  FStar_Range.range ->
    FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  ->
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____232 =
            let uu____233 =
              let uu____234 =
                let uu____235 = embed_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____235  in
              [uu____234]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____233
             in
          uu____232 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____239 =
            let uu____240 =
              let uu____241 =
                let uu____242 = embed_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____242  in
              [uu____241]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____240
             in
          uu____239 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____246 =
            let uu____247 =
              let uu____248 =
                let uu____249 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____249  in
              [uu____248]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____247
             in
          uu____246 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____254 =
            let uu____255 =
              let uu____256 =
                let uu____257 = embed_term rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____257  in
              let uu____258 =
                let uu____261 =
                  let uu____262 = embed_argv rng a  in
                  FStar_Syntax_Syntax.as_arg uu____262  in
                [uu____261]  in
              uu____256 :: uu____258  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____255
             in
          uu____254 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____267 =
            let uu____268 =
              let uu____269 =
                let uu____270 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____270  in
              let uu____271 =
                let uu____274 =
                  let uu____275 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____275  in
                [uu____274]  in
              uu____269 :: uu____271  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____268
             in
          uu____267 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____280 =
            let uu____281 =
              let uu____282 =
                let uu____283 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____283  in
              let uu____284 =
                let uu____287 =
                  let uu____288 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____288  in
                [uu____287]  in
              uu____282 :: uu____284  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____281
             in
          uu____280 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____292 =
            let uu____293 =
              let uu____294 =
                let uu____295 = FStar_Syntax_Embeddings.embed_unit rng ()  in
                FStar_Syntax_Syntax.as_arg uu____295  in
              [uu____294]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____293
             in
          uu____292 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____300 =
            let uu____301 =
              let uu____302 =
                let uu____303 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____303  in
              let uu____304 =
                let uu____307 =
                  let uu____308 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____308  in
                [uu____307]  in
              uu____302 :: uu____304  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____301
             in
          uu____300 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____312 =
            let uu____313 =
              let uu____314 =
                let uu____315 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____315  in
              [uu____314]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____313
             in
          uu____312 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____320 =
            let uu____321 =
              let uu____322 =
                let uu____323 = FStar_Syntax_Embeddings.embed_int rng u  in
                FStar_Syntax_Syntax.as_arg uu____323  in
              let uu____324 =
                let uu____327 =
                  let uu____328 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____328  in
                [uu____327]  in
              uu____322 :: uu____324  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____321
             in
          uu____320 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____335 =
            let uu____336 =
              let uu____337 =
                let uu____338 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____338  in
              let uu____339 =
                let uu____342 =
                  let uu____343 = embed_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____343  in
                let uu____344 =
                  let uu____347 =
                    let uu____348 = embed_term rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____348  in
                  let uu____349 =
                    let uu____352 =
                      let uu____353 = embed_term rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____353  in
                    [uu____352]  in
                  uu____347 :: uu____349  in
                uu____342 :: uu____344  in
              uu____337 :: uu____339  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____336
             in
          uu____335 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____362 =
            let uu____363 =
              let uu____364 =
                let uu____365 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____365  in
              let uu____366 =
                let uu____369 =
                  let uu____370 =
                    let uu____371 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____371 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____370  in
                [uu____369]  in
              uu____364 :: uu____366  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____363
             in
          uu____362 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____388 =
            let uu____389 =
              let uu____390 =
                let uu____391 = embed_term rng e  in
                FStar_Syntax_Syntax.as_arg uu____391  in
              let uu____392 =
                let uu____395 =
                  let uu____396 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____396  in
                let uu____397 =
                  let uu____400 =
                    let uu____401 =
                      let uu____402 =
                        FStar_Syntax_Embeddings.embed_option embed_term
                          FStar_Reflection_Data.fstar_refl_term
                         in
                      uu____402 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____401  in
                  [uu____400]  in
                uu____395 :: uu____397  in
              uu____390 :: uu____392  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____389
             in
          uu____388 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____419 =
            let uu____420 =
              let uu____421 =
                let uu____422 = embed_term rng e  in
                FStar_Syntax_Syntax.as_arg uu____422  in
              let uu____423 =
                let uu____426 =
                  let uu____427 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____427  in
                let uu____428 =
                  let uu____431 =
                    let uu____432 =
                      let uu____433 =
                        FStar_Syntax_Embeddings.embed_option embed_term
                          FStar_Reflection_Data.fstar_refl_term
                         in
                      uu____433 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____432  in
                  [uu____431]  in
                uu____426 :: uu____428  in
              uu____421 :: uu____423  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____420
             in
          uu____419 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___53_443 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___53_443.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___53_443.FStar_Syntax_Syntax.vars)
          }
  
let (embed_bv_view :
  FStar_Range.range ->
    FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun bvv  ->
      let uu____453 =
        let uu____454 =
          let uu____455 =
            let uu____456 =
              FStar_Syntax_Embeddings.embed_string rng
                bvv.FStar_Reflection_Data.bv_ppname
               in
            FStar_Syntax_Syntax.as_arg uu____456  in
          let uu____457 =
            let uu____460 =
              let uu____461 =
                FStar_Syntax_Embeddings.embed_int rng
                  bvv.FStar_Reflection_Data.bv_index
                 in
              FStar_Syntax_Syntax.as_arg uu____461  in
            let uu____462 =
              let uu____465 =
                let uu____466 =
                  embed_term rng bvv.FStar_Reflection_Data.bv_sort  in
                FStar_Syntax_Syntax.as_arg uu____466  in
              [uu____465]  in
            uu____460 :: uu____462  in
          uu____455 :: uu____457  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____454
         in
      uu____453 FStar_Pervasives_Native.None rng
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total (t,md) ->
          let uu____484 =
            let uu____485 =
              let uu____486 =
                let uu____487 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____487  in
              let uu____488 =
                let uu____491 =
                  let uu____492 =
                    let uu____493 =
                      FStar_Syntax_Embeddings.embed_option embed_term
                        FStar_Syntax_Syntax.t_term
                       in
                    uu____493 rng md  in
                  FStar_Syntax_Syntax.as_arg uu____492  in
                [uu____491]  in
              uu____486 :: uu____488  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____485
             in
          uu____484 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____508 =
            let uu____509 =
              let uu____510 =
                let uu____511 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____511  in
              let uu____512 =
                let uu____515 =
                  let uu____516 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____516  in
                [uu____515]  in
              uu____510 :: uu____512  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____509
             in
          uu____508 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___54_519 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___54_519.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___54_519.FStar_Syntax_Syntax.vars)
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
      let uu___55_530 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_530.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_530.FStar_Syntax_Syntax.vars)
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
          let uu____553 =
            let uu____554 =
              let uu____555 =
                let uu____556 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____556  in
              let uu____557 =
                let uu____560 =
                  let uu____561 = embed_fv rng fv  in
                  FStar_Syntax_Syntax.as_arg uu____561  in
                let uu____562 =
                  let uu____565 =
                    let uu____566 = embed_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____566  in
                  let uu____567 =
                    let uu____570 =
                      let uu____571 = embed_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____571  in
                    [uu____570]  in
                  uu____565 :: uu____567  in
                uu____560 :: uu____562  in
              uu____555 :: uu____557  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____554
             in
          uu____553 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
          let uu____576 =
            let uu____577 =
              let uu____578 =
                let uu____579 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____579  in
              let uu____580 =
                let uu____583 =
                  let uu____584 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____584  in
                [uu____583]  in
              uu____578 :: uu____580  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
              uu____577
             in
          uu____576 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____599 =
            let uu____600 =
              let uu____601 =
                let uu____602 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____602  in
              let uu____603 =
                let uu____606 =
                  let uu____607 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____607  in
                let uu____608 =
                  let uu____611 =
                    let uu____612 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____612  in
                  let uu____613 =
                    let uu____616 =
                      let uu____617 =
                        let uu____618 =
                          let uu____625 =
                            FStar_Syntax_Syntax.t_list_of
                              FStar_Syntax_Syntax.t_string
                             in
                          FStar_Syntax_Embeddings.embed_list
                            FStar_Syntax_Embeddings.embed_string_list
                            uu____625
                           in
                        uu____618 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____617  in
                    [uu____616]  in
                  uu____611 :: uu____613  in
                uu____606 :: uu____608  in
              uu____601 :: uu____603  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____600
             in
          uu____599 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___56_633 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___56_633.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___56_633.FStar_Syntax_Syntax.vars)
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
            let uu____643 =
              let uu____644 =
                let uu____645 =
                  let uu____646 =
                    let uu____647 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____647  in
                  FStar_Syntax_Syntax.as_arg uu____646  in
                [uu____645]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
                uu____644
               in
            uu____643 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.Mult (e1,e2) ->
            let uu____652 =
              let uu____653 =
                let uu____654 =
                  let uu____655 = embed_exp rng e1  in
                  FStar_Syntax_Syntax.as_arg uu____655  in
                let uu____656 =
                  let uu____659 =
                    let uu____660 = embed_exp rng e2  in
                    FStar_Syntax_Syntax.as_arg uu____660  in
                  [uu____659]  in
                uu____654 :: uu____656  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
                uu____653
               in
            uu____652 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___57_663 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___57_663.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___57_663.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_bv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____673 =
      let uu____674 = FStar_Syntax_Subst.compress t  in
      uu____674.FStar_Syntax_Syntax.n  in
    match uu____673 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____680 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____680
    | uu____681 ->
        ((let uu____683 =
            let uu____688 =
              let uu____689 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____689  in
            (FStar_Errors.Warning_NotEmbedded, uu____688)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____683);
         FStar_Pervasives_Native.None)
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____699 =
      let uu____700 = FStar_Syntax_Subst.compress t  in
      uu____700.FStar_Syntax_Syntax.n  in
    match uu____699 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____706 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____706
    | uu____707 ->
        ((let uu____709 =
            let uu____714 =
              let uu____715 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____715  in
            (FStar_Errors.Warning_NotEmbedded, uu____714)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____709);
         FStar_Pervasives_Native.None)
  
let rec mapM_opt :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> FStar_Pervasives_Native.Some []
      | x::xs ->
          let uu____755 = f x  in
          FStar_Util.bind_opt uu____755
            (fun x1  ->
               let uu____763 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____763
                 (fun xs1  -> FStar_Pervasives_Native.Some (x1 :: xs1)))
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let aqs =
          mapM_opt
            (fun uu____811  ->
               match uu____811 with
               | (bv,b,e) ->
                   if b
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.NT (bv, e))
                   else
                     (let uu____834 = unembed_term e  in
                      FStar_Util.bind_opt uu____834
                        (fun e1  ->
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.NT (bv, e1)))))
            qi.FStar_Syntax_Syntax.antiquotes
           in
        FStar_Util.bind_opt aqs
          (fun s  ->
             let uu____846 = FStar_Syntax_Subst.subst s tm  in
             FStar_Pervasives_Native.Some uu____846)
    | uu____847 ->
        ((let uu____849 =
            let uu____854 =
              let uu____855 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____855  in
            (FStar_Errors.Warning_NotEmbedded, uu____854)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____849);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
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
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____962 ->
             ((let uu____976 =
                 let uu____981 =
                   let uu____982 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____982
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____981)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____976);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____990 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____990 t
  
let (unembed_fv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____1006 =
      let uu____1007 = FStar_Syntax_Subst.compress t  in
      uu____1007.FStar_Syntax_Syntax.n  in
    match uu____1006 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____1013 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____1013
    | uu____1014 ->
        ((let uu____1016 =
            let uu____1021 =
              let uu____1022 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____1022  in
            (FStar_Errors.Warning_NotEmbedded, uu____1021)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1016);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____1032 =
      let uu____1033 = FStar_Syntax_Subst.compress t  in
      uu____1033.FStar_Syntax_Syntax.n  in
    match uu____1032 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____1039 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____1039
    | uu____1040 ->
        ((let uu____1042 =
            let uu____1047 =
              let uu____1048 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____1048  in
            (FStar_Errors.Warning_NotEmbedded, uu____1047)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1042);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____1058 =
      let uu____1059 = FStar_Syntax_Subst.compress t  in
      uu____1059.FStar_Syntax_Syntax.n  in
    match uu____1058 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____1065 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____1065
    | uu____1066 ->
        ((let uu____1068 =
            let uu____1073 =
              let uu____1074 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____1074  in
            (FStar_Errors.Warning_NotEmbedded, uu____1073)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1068);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1085 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1085 with
    | (hd1,args) ->
        let uu____1124 =
          let uu____1137 =
            let uu____1138 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1138.FStar_Syntax_Syntax.n  in
          (uu____1137, args)  in
        (match uu____1124 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1198)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1223 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____1223
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1232)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1257 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____1257
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1264 ->
             ((let uu____1278 =
                 let uu____1283 =
                   let uu____1284 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____1284
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1283)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1278);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1293 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1293 with
    | (hd1,args) ->
        let uu____1332 =
          let uu____1345 =
            let uu____1346 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1346.FStar_Syntax_Syntax.n  in
          (uu____1345, args)  in
        (match uu____1332 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1361)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1386 = unembed_const c  in
             FStar_Util.bind_opt uu____1386
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1395)::(ps,uu____1397)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1432 = unembed_fv f  in
             FStar_Util.bind_opt uu____1432
               (fun f1  ->
                  let uu____1438 =
                    let uu____1443 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1443 ps  in
                  FStar_Util.bind_opt uu____1438
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1462)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1487 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1487
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var bv1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1496)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1521 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1521
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild bv1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(bv,uu____1530)::(t2,uu____1532)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
             ->
             let uu____1567 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1567
               (fun bv1  ->
                  let uu____1573 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1573
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                         (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
         | uu____1580 ->
             ((let uu____1594 =
                 let uu____1599 =
                   let uu____1600 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1600
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1599)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1594);
              FStar_Pervasives_Native.None))
  
let (unembed_branch :
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_tuple2 unembed_pattern unembed_term 
let (unembed_argv :
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_tuple2 unembed_term unembed_aqualv 
let (unembed_term_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____1630 = FStar_Syntax_Util.head_and_args t  in
    match uu____1630 with
    | (hd1,args) ->
        let uu____1669 =
          let uu____1682 =
            let uu____1683 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1683.FStar_Syntax_Syntax.n  in
          (uu____1682, args)  in
        (match uu____1669 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1698)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1723 = unembed_bv b  in
             FStar_Util.bind_opt uu____1723
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1732)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
             ->
             let uu____1757 = unembed_bv b  in
             FStar_Util.bind_opt uu____1757
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                    (FStar_Reflection_Data.Tv_BVar b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1766)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1791 = unembed_fv f  in
             FStar_Util.bind_opt uu____1791
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1800)::(r,uu____1802)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1837 = unembed_term l  in
             FStar_Util.bind_opt uu____1837
               (fun l1  ->
                  let uu____1843 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1843
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1868)::(t1,uu____1870)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1905 = unembed_binder b  in
             FStar_Util.bind_opt uu____1905
               (fun b1  ->
                  let uu____1911 = unembed_term t1  in
                  FStar_Util.bind_opt uu____1911
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                         (FStar_Reflection_Data.Tv_Abs (b1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1920)::(t1,uu____1922)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1957 = unembed_binder b  in
             FStar_Util.bind_opt uu____1957
               (fun b1  ->
                  let uu____1963 = unembed_comp t1  in
                  FStar_Util.bind_opt uu____1963
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1972)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1997 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1997
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2006)::(t1,uu____2008)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____2043 = unembed_bv b  in
             FStar_Util.bind_opt uu____2043
               (fun b1  ->
                  let uu____2049 = unembed_term t1  in
                  FStar_Util.bind_opt uu____2049
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Refine (b1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2058)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____2083 = unembed_const c  in
             FStar_Util.bind_opt uu____2083
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____2092)::(t1,uu____2094)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____2129 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____2129
               (fun u1  ->
                  let uu____2135 = unembed_term t1  in
                  FStar_Util.bind_opt uu____2135
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_56  -> FStar_Pervasives_Native.Some _0_56)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____2144)::(b,uu____2146)::(t1,uu____2148)::(t2,uu____2150)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____2205 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____2205
               (fun r1  ->
                  let uu____2211 = unembed_bv b  in
                  FStar_Util.bind_opt uu____2211
                    (fun b1  ->
                       let uu____2217 = unembed_term t1  in
                       FStar_Util.bind_opt uu____2217
                         (fun t11  ->
                            let uu____2223 = unembed_term t2  in
                            FStar_Util.bind_opt uu____2223
                              (fun t21  ->
                                 FStar_All.pipe_left
                                   (fun _0_57  ->
                                      FStar_Pervasives_Native.Some _0_57)
                                   (FStar_Reflection_Data.Tv_Let
                                      (r1, b1, t11, t21))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t1,uu____2232)::(brs,uu____2234)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____2269 = unembed_term t1  in
             FStar_Util.bind_opt uu____2269
               (fun t2  ->
                  let uu____2275 =
                    let uu____2284 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____2284 brs  in
                  FStar_Util.bind_opt uu____2275
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                         (FStar_Reflection_Data.Tv_Match (t2, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e,uu____2323)::(t1,uu____2325)::(tacopt,uu____2327)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
             ->
             let uu____2372 = unembed_term e  in
             FStar_Util.bind_opt uu____2372
               (fun e1  ->
                  let uu____2378 = unembed_term t1  in
                  FStar_Util.bind_opt uu____2378
                    (fun t2  ->
                       let uu____2384 =
                         let uu____2389 =
                           FStar_Syntax_Embeddings.unembed_option
                             unembed_term
                            in
                         uu____2389 tacopt  in
                       FStar_Util.bind_opt uu____2384
                         (fun tacopt1  ->
                            FStar_All.pipe_left
                              (fun _0_59  ->
                                 FStar_Pervasives_Native.Some _0_59)
                              (FStar_Reflection_Data.Tv_AscribedT
                                 (e1, t2, tacopt1)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e,uu____2408)::(c,uu____2410)::(tacopt,uu____2412)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
             ->
             let uu____2457 = unembed_term e  in
             FStar_Util.bind_opt uu____2457
               (fun e1  ->
                  let uu____2463 = unembed_comp c  in
                  FStar_Util.bind_opt uu____2463
                    (fun c1  ->
                       let uu____2469 =
                         let uu____2474 =
                           FStar_Syntax_Embeddings.unembed_option
                             unembed_term
                            in
                         uu____2474 tacopt  in
                       FStar_Util.bind_opt uu____2469
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
         | uu____2508 ->
             ((let uu____2522 =
                 let uu____2527 =
                   let uu____2528 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____2528
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2527)  in
               FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2522);
              FStar_Pervasives_Native.None))
  
let (unembed_bv_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.bv_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2539 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2539 with
    | (hd1,args) ->
        let uu____2578 =
          let uu____2591 =
            let uu____2592 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2592.FStar_Syntax_Syntax.n  in
          (uu____2591, args)  in
        (match uu____2578 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2607)::(idx,uu____2609)::(s,uu____2611)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2656 = FStar_Syntax_Embeddings.unembed_string nm  in
             FStar_Util.bind_opt uu____2656
               (fun nm1  ->
                  let uu____2662 = FStar_Syntax_Embeddings.unembed_int idx
                     in
                  FStar_Util.bind_opt uu____2662
                    (fun idx1  ->
                       let uu____2668 = unembed_term s  in
                       FStar_Util.bind_opt uu____2668
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_62  ->
                                 FStar_Pervasives_Native.Some _0_62)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2675 ->
             ((let uu____2689 =
                 let uu____2694 =
                   let uu____2695 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded bv_view: %s"
                     uu____2695
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2694)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2689);
              FStar_Pervasives_Native.None))
  
let rec (unembed_exp :
  FStar_Reflection_Data.exp FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2704 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2704 with
    | (hd1,args) ->
        let uu____2743 =
          let uu____2756 =
            let uu____2757 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2757.FStar_Syntax_Syntax.n  in
          (uu____2756, args)  in
        (match uu____2743 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____2787)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____2812 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____2812
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_63  -> FStar_Pervasives_Native.Some _0_63)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____2821)::(e2,uu____2823)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____2858 = unembed_exp e1  in
             FStar_Util.bind_opt uu____2858
               (fun e11  ->
                  let uu____2864 = unembed_exp e2  in
                  FStar_Util.bind_opt uu____2864
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____2871 ->
             ((let uu____2885 =
                 let uu____2890 =
                   let uu____2891 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded exp: %s" uu____2891
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2890)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2885);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2902 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2902 with
    | (hd1,args) ->
        let uu____2941 =
          let uu____2954 =
            let uu____2955 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2955.FStar_Syntax_Syntax.n  in
          (uu____2954, args)  in
        (match uu____2941 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2970)::(md,uu____2972)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____3007 = unembed_term t2  in
             FStar_Util.bind_opt uu____3007
               (fun t3  ->
                  let uu____3013 =
                    let uu____3018 =
                      FStar_Syntax_Embeddings.unembed_option unembed_term  in
                    uu____3018 md  in
                  FStar_Util.bind_opt uu____3013
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_65  -> FStar_Pervasives_Native.Some _0_65)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____3037)::(post,uu____3039)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____3074 = unembed_term pre  in
             FStar_Util.bind_opt uu____3074
               (fun pre1  ->
                  let uu____3080 = unembed_term post  in
                  FStar_Util.bind_opt uu____3080
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
         | uu____3104 ->
             ((let uu____3118 =
                 let uu____3123 =
                   let uu____3124 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____3124
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3123)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3118);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3135 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3135 with
    | (hd1,args) ->
        let uu____3174 =
          let uu____3187 =
            let uu____3188 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3188.FStar_Syntax_Syntax.n  in
          (uu____3187, args)  in
        (match uu____3174 with
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
         | uu____3246 ->
             ((let uu____3260 =
                 let uu____3265 =
                   let uu____3266 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____3266
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3265)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3260);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____3276 =
      let uu____3277 = FStar_Syntax_Subst.compress t  in
      uu____3277.FStar_Syntax_Syntax.n  in
    match uu____3276 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____3283 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____3283
    | uu____3284 ->
        ((let uu____3286 =
            let uu____3291 =
              let uu____3292 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3292  in
            (FStar_Errors.Warning_NotEmbedded, uu____3291)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____3286);
         FStar_Pervasives_Native.None)
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3303 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3303 with
    | (hd1,args) ->
        let uu____3342 =
          let uu____3355 =
            let uu____3356 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3356.FStar_Syntax_Syntax.n  in
          (uu____3355, args)  in
        (match uu____3342 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3371)::(bs,uu____3373)::(t2,uu____3375)::(dcs,uu____3377)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3432 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3432
               (fun nm1  ->
                  let uu____3444 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____3444
                    (fun bs1  ->
                       let uu____3450 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3450
                         (fun t3  ->
                            let uu____3456 =
                              let uu____3463 =
                                let uu____3470 =
                                  FStar_Syntax_Embeddings.unembed_list
                                    FStar_Syntax_Embeddings.unembed_string
                                   in
                                FStar_Syntax_Embeddings.unembed_list
                                  uu____3470
                                 in
                              uu____3463 dcs  in
                            FStar_Util.bind_opt uu____3456
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_Pervasives_Native.Some _0_68)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____3503)::(fvar1,uu____3505)::(ty,uu____3507)::(t2,uu____3509)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____3564 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____3564
               (fun r1  ->
                  let uu____3570 = unembed_fv fvar1  in
                  FStar_Util.bind_opt uu____3570
                    (fun fvar2  ->
                       let uu____3576 = unembed_term ty  in
                       FStar_Util.bind_opt uu____3576
                         (fun ty1  ->
                            let uu____3582 = unembed_term t2  in
                            FStar_Util.bind_opt uu____3582
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
         | uu____3604 ->
             ((let uu____3618 =
                 let uu____3623 =
                   let uu____3624 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____3624
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3623)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3618);
              FStar_Pervasives_Native.None))
  
let (embed_binder_view :
  (FStar_Syntax_Syntax.bv,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedder)
  =
  FStar_Syntax_Embeddings.embed_tuple2 embed_bv
    FStar_Reflection_Data.fstar_refl_bv_view embed_aqualv
    FStar_Reflection_Data.fstar_refl_aqualv
  
let (unembed_binder_view :
  (FStar_Syntax_Syntax.bv,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_tuple2 unembed_bv unembed_aqualv 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3651 =
      let uu____3652 =
        let uu____3653 =
          let uu____3654 =
            let uu____3655 = FStar_Reflection_Basic.inspect_bv bv  in
            embed_bv_view i.FStar_Syntax_Syntax.rng uu____3655  in
          FStar_Syntax_Syntax.as_arg uu____3654  in
        [uu____3653]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____3652
       in
    uu____3651 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3662 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____3662 with
    | (bv,aq) ->
        let uu____3669 =
          let uu____3670 =
            let uu____3671 =
              let uu____3672 = embed_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____3672  in
            let uu____3673 =
              let uu____3676 =
                let uu____3677 = embed_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____3677  in
              [uu____3676]  in
            uu____3671 :: uu____3673  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____3670
           in
        uu____3669 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3684 =
      let uu____3685 =
        let uu____3686 =
          let uu____3687 =
            let uu____3688 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____3691 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____3691 i.FStar_Syntax_Syntax.rng uu____3688  in
          FStar_Syntax_Syntax.as_arg uu____3687  in
        [uu____3686]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____3685
       in
    uu____3684 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3705 =
      let uu____3706 =
        let uu____3707 =
          let uu____3708 =
            let uu____3709 = FStar_Reflection_Basic.inspect_comp comp  in
            embed_comp_view i.FStar_Syntax_Syntax.rng uu____3709  in
          FStar_Syntax_Syntax.as_arg uu____3708  in
        [uu____3707]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____3706
       in
    uu____3705 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3719 =
      let uu____3720 =
        let uu____3721 =
          let uu____3722 =
            let uu____3723 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed_sigelt_view i.FStar_Syntax_Syntax.rng uu____3723  in
          FStar_Syntax_Syntax.as_arg uu____3722  in
        [uu____3721]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____3720
       in
    uu____3719 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  