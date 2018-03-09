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
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____298 =
            let uu____299 =
              let uu____300 =
                let uu____301 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____301  in
              let uu____302 =
                let uu____305 =
                  let uu____306 = embed_binder rng b  in
                  FStar_Syntax_Syntax.as_arg uu____306  in
                let uu____307 =
                  let uu____310 =
                    let uu____311 = embed_term rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____311  in
                  let uu____312 =
                    let uu____315 =
                      let uu____316 = embed_term rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____316  in
                    [uu____315]  in
                  uu____310 :: uu____312  in
                uu____305 :: uu____307  in
              uu____300 :: uu____302  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____299
             in
          uu____298 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____325 =
            let uu____326 =
              let uu____327 =
                let uu____328 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____328  in
              let uu____329 =
                let uu____332 =
                  let uu____333 =
                    let uu____334 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____334 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____333  in
                [uu____332]  in
              uu____327 :: uu____329  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____326
             in
          uu____325 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___53_344 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___53_344.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___53_344.FStar_Syntax_Syntax.vars)
          }
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____355 =
            let uu____356 =
              let uu____357 =
                let uu____358 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____358  in
              [uu____357]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____356
             in
          uu____355 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____366 =
            let uu____367 =
              let uu____368 =
                let uu____369 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____369  in
              let uu____370 =
                let uu____373 =
                  let uu____374 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____374  in
                [uu____373]  in
              uu____368 :: uu____370  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____367
             in
          uu____366 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___54_377 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___54_377.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___54_377.FStar_Syntax_Syntax.vars)
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
      let uu___55_388 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_388.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_388.FStar_Syntax_Syntax.vars)
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
          let uu____411 =
            let uu____412 =
              let uu____413 =
                let uu____414 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____414  in
              let uu____415 =
                let uu____418 =
                  let uu____419 = embed_fvar rng fv  in
                  FStar_Syntax_Syntax.as_arg uu____419  in
                let uu____420 =
                  let uu____423 =
                    let uu____424 = embed_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____424  in
                  let uu____425 =
                    let uu____428 =
                      let uu____429 = embed_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____429  in
                    [uu____428]  in
                  uu____423 :: uu____425  in
                uu____418 :: uu____420  in
              uu____413 :: uu____415  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____412
             in
          uu____411 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
          let uu____434 =
            let uu____435 =
              let uu____436 =
                let uu____437 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____437  in
              let uu____438 =
                let uu____441 =
                  let uu____442 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____442  in
                [uu____441]  in
              uu____436 :: uu____438  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
              uu____435
             in
          uu____434 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____457 =
            let uu____458 =
              let uu____459 =
                let uu____460 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____460  in
              let uu____461 =
                let uu____464 =
                  let uu____465 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____465  in
                let uu____466 =
                  let uu____469 =
                    let uu____470 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____470  in
                  let uu____471 =
                    let uu____474 =
                      let uu____475 =
                        let uu____476 =
                          let uu____483 =
                            FStar_Syntax_Syntax.t_list_of
                              FStar_Syntax_Syntax.t_string
                             in
                          FStar_Syntax_Embeddings.embed_list
                            FStar_Syntax_Embeddings.embed_string_list
                            uu____483
                           in
                        uu____476 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____475  in
                    [uu____474]  in
                  uu____469 :: uu____471  in
                uu____464 :: uu____466  in
              uu____459 :: uu____461  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____458
             in
          uu____457 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___56_491 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___56_491.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___56_491.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____501 =
      let uu____502 = FStar_Syntax_Subst.compress t  in
      uu____502.FStar_Syntax_Syntax.n  in
    match uu____501 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____508 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____508
    | uu____509 ->
        ((let uu____511 =
            let uu____516 =
              let uu____517 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____517  in
            (FStar_Errors.Warning_NotEmbedded, uu____516)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____511);
         FStar_Pervasives_Native.None)
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____528;
           FStar_Syntax_Syntax.pos = uu____529;
           FStar_Syntax_Syntax.vars = uu____530;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> FStar_Pervasives_Native.Some qt
    | uu____543 ->
        ((let uu____545 =
            let uu____550 =
              let uu____551 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____551  in
            (FStar_Errors.Warning_NotEmbedded, uu____550)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____545);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____562 = FStar_Syntax_Util.head_and_args t1  in
    match uu____562 with
    | (hd1,args) ->
        let uu____601 =
          let uu____614 =
            let uu____615 = FStar_Syntax_Util.un_uinst hd1  in
            uu____615.FStar_Syntax_Syntax.n  in
          (uu____614, args)  in
        (match uu____601 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____658 ->
             ((let uu____672 =
                 let uu____677 =
                   let uu____678 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____678
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____677)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____672);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____686 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____686 t
  
let (unembed_fvar :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____702 =
      let uu____703 = FStar_Syntax_Subst.compress t  in
      uu____703.FStar_Syntax_Syntax.n  in
    match uu____702 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____709 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____709
    | uu____710 ->
        ((let uu____712 =
            let uu____717 =
              let uu____718 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____718  in
            (FStar_Errors.Warning_NotEmbedded, uu____717)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____712);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____728 =
      let uu____729 = FStar_Syntax_Subst.compress t  in
      uu____729.FStar_Syntax_Syntax.n  in
    match uu____728 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____735 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____735
    | uu____736 ->
        ((let uu____738 =
            let uu____743 =
              let uu____744 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____744  in
            (FStar_Errors.Warning_NotEmbedded, uu____743)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____738);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____754 =
      let uu____755 = FStar_Syntax_Subst.compress t  in
      uu____755.FStar_Syntax_Syntax.n  in
    match uu____754 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____761 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____761
    | uu____762 ->
        ((let uu____764 =
            let uu____769 =
              let uu____770 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____770  in
            (FStar_Errors.Warning_NotEmbedded, uu____769)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____764);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____781 = FStar_Syntax_Util.head_and_args t1  in
    match uu____781 with
    | (hd1,args) ->
        let uu____820 =
          let uu____833 =
            let uu____834 = FStar_Syntax_Util.un_uinst hd1  in
            uu____834.FStar_Syntax_Syntax.n  in
          (uu____833, args)  in
        (match uu____820 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____894)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____919 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____919
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____928)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____953 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____953
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____960 ->
             ((let uu____974 =
                 let uu____979 =
                   let uu____980 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____980
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____979)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____974);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____989 = FStar_Syntax_Util.head_and_args t1  in
    match uu____989 with
    | (hd1,args) ->
        let uu____1028 =
          let uu____1041 =
            let uu____1042 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1042.FStar_Syntax_Syntax.n  in
          (uu____1041, args)  in
        (match uu____1028 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1057)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1082 = unembed_const c  in
             FStar_Util.bind_opt uu____1082
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1091)::(ps,uu____1093)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1128 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1128
               (fun f1  ->
                  let uu____1134 =
                    let uu____1139 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1139 ps  in
                  FStar_Util.bind_opt uu____1134
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1158)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1183 = unembed_binder b  in
             FStar_Util.bind_opt uu____1183
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1192)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1217 = unembed_binder b  in
             FStar_Util.bind_opt uu____1217
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild b1))
         | uu____1224 ->
             ((let uu____1238 =
                 let uu____1243 =
                   let uu____1244 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1244
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1243)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1238);
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
    let uu____1275 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1275 with
    | (hd1,args) ->
        let uu____1314 =
          let uu____1327 =
            let uu____1328 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1328.FStar_Syntax_Syntax.n  in
          (uu____1327, args)  in
        (match uu____1314 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1343)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1368 = unembed_binder b  in
             FStar_Util.bind_opt uu____1368
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1377)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1402 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1402
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1411)::(r,uu____1413)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1448 = unembed_term l  in
             FStar_Util.bind_opt uu____1448
               (fun l1  ->
                  let uu____1454 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1454
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1479)::(t2,uu____1481)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1516 = unembed_binder b  in
             FStar_Util.bind_opt uu____1516
               (fun b1  ->
                  let uu____1522 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1522
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1531)::(t2,uu____1533)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1568 = unembed_binder b  in
             FStar_Util.bind_opt uu____1568
               (fun b1  ->
                  let uu____1574 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1574
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1583)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1608 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1608
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1617)::(t2,uu____1619)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1654 = unembed_binder b  in
             FStar_Util.bind_opt uu____1654
               (fun b1  ->
                  let uu____1660 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1660
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1669)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1694 = unembed_const c  in
             FStar_Util.bind_opt uu____1694
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1703)::(t2,uu____1705)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1740 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1740
               (fun u1  ->
                  let uu____1746 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1746
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____1755)::(b,uu____1757)::(t11,uu____1759)::(t2,uu____1761)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____1816 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____1816
               (fun r1  ->
                  let uu____1822 = unembed_binder b  in
                  FStar_Util.bind_opt uu____1822
                    (fun b1  ->
                       let uu____1828 = unembed_term t11  in
                       FStar_Util.bind_opt uu____1828
                         (fun t12  ->
                            let uu____1834 = unembed_term t2  in
                            FStar_Util.bind_opt uu____1834
                              (fun t21  ->
                                 FStar_All.pipe_left
                                   (fun _0_55  ->
                                      FStar_Pervasives_Native.Some _0_55)
                                   (FStar_Reflection_Data.Tv_Let
                                      (r1, b1, t12, t21))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1843)::(brs,uu____1845)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____1880 = unembed_term t2  in
             FStar_Util.bind_opt uu____1880
               (fun t3  ->
                  let uu____1886 =
                    let uu____1895 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____1895 brs  in
                  FStar_Util.bind_opt uu____1886
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
         | uu____1949 ->
             ((let uu____1963 =
                 let uu____1968 =
                   let uu____1969 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____1969
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1968)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1963);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1980 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1980 with
    | (hd1,args) ->
        let uu____2019 =
          let uu____2032 =
            let uu____2033 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2033.FStar_Syntax_Syntax.n  in
          (uu____2032, args)  in
        (match uu____2019 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____2048)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2073 = unembed_term t2  in
             FStar_Util.bind_opt uu____2073
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2082)::(post,uu____2084)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2119 = unembed_term pre  in
             FStar_Util.bind_opt uu____2119
               (fun pre1  ->
                  let uu____2125 = unembed_term post  in
                  FStar_Util.bind_opt uu____2125
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
         | uu____2149 ->
             ((let uu____2163 =
                 let uu____2168 =
                   let uu____2169 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2169
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2168)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2163);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2180 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2180 with
    | (hd1,args) ->
        let uu____2219 =
          let uu____2232 =
            let uu____2233 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2233.FStar_Syntax_Syntax.n  in
          (uu____2232, args)  in
        (match uu____2219 with
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
         | uu____2291 ->
             ((let uu____2305 =
                 let uu____2310 =
                   let uu____2311 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____2311
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2310)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2305);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____2321 =
      let uu____2322 = FStar_Syntax_Subst.compress t  in
      uu____2322.FStar_Syntax_Syntax.n  in
    match uu____2321 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____2328 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____2328
    | uu____2329 ->
        ((let uu____2331 =
            let uu____2336 =
              let uu____2337 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____2337  in
            (FStar_Errors.Warning_NotEmbedded, uu____2336)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2331);
         FStar_Pervasives_Native.None)
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2348 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2348 with
    | (hd1,args) ->
        let uu____2387 =
          let uu____2400 =
            let uu____2401 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2401.FStar_Syntax_Syntax.n  in
          (uu____2400, args)  in
        (match uu____2387 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2416)::(bs,uu____2418)::(t2,uu____2420)::(dcs,uu____2422)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____2477 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____2477
               (fun nm1  ->
                  let uu____2489 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____2489
                    (fun bs1  ->
                       let uu____2495 = unembed_term t2  in
                       FStar_Util.bind_opt uu____2495
                         (fun t3  ->
                            let uu____2501 =
                              let uu____2508 =
                                let uu____2515 =
                                  FStar_Syntax_Embeddings.unembed_list
                                    FStar_Syntax_Embeddings.unembed_string
                                   in
                                FStar_Syntax_Embeddings.unembed_list
                                  uu____2515
                                 in
                              uu____2508 dcs  in
                            FStar_Util.bind_opt uu____2501
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_Pervasives_Native.Some _0_61)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____2548)::(fvar1,uu____2550)::(ty,uu____2552)::(t2,uu____2554)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____2609 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____2609
               (fun r1  ->
                  let uu____2615 = unembed_fvar fvar1  in
                  FStar_Util.bind_opt uu____2615
                    (fun fvar2  ->
                       let uu____2621 = unembed_term ty  in
                       FStar_Util.bind_opt uu____2621
                         (fun ty1  ->
                            let uu____2627 = unembed_term t2  in
                            FStar_Util.bind_opt uu____2627
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____2649 ->
             ((let uu____2663 =
                 let uu____2668 =
                   let uu____2669 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____2669
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2668)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2663);
              FStar_Pervasives_Native.None))
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____2677 =
      let uu____2678 =
        let uu____2679 =
          let uu____2680 =
            let uu____2681 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____2684 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____2684 i.FStar_Syntax_Syntax.rng uu____2681  in
          FStar_Syntax_Syntax.as_arg uu____2680  in
        [uu____2679]  in
      FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv
        uu____2678
       in
    uu____2677 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 