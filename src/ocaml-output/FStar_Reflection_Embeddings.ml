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
  
let (embed_term_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedder)
  =
  fun aq  ->
    fun rng  ->
      fun t  ->
        let qi =
          {
            FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
            FStar_Syntax_Syntax.antiquotes = aq
          }  in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (t, qi))
          FStar_Pervasives_Native.None rng
  
let (embed_term :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun rng  -> fun t  -> let uu____42 = embed_term_aq []  in uu____42 rng t 
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
      let uu___122_66 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___122_66.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___122_66.FStar_Syntax_Syntax.vars)
      }
  
let (embed_binders :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun l  ->
      let uu____76 =
        FStar_Syntax_Embeddings.embed_list embed_binder
          FStar_Reflection_Data.fstar_refl_binder
         in
      uu____76 rng l
  
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
            let uu____122 =
              let uu____123 =
                let uu____124 =
                  let uu____125 =
                    let uu____126 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____126  in
                  FStar_Syntax_Syntax.as_arg uu____125  in
                [uu____124]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
                uu____123
               in
            uu____122 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____130 =
              let uu____131 =
                let uu____132 =
                  let uu____133 = FStar_Syntax_Embeddings.embed_string rng s
                     in
                  FStar_Syntax_Syntax.as_arg uu____133  in
                [uu____132]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
                uu____131
               in
            uu____130 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___123_136 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___123_136.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___123_136.FStar_Syntax_Syntax.vars)
      }
  
let rec (embed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedder) =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____145 =
            let uu____146 =
              let uu____147 =
                let uu____148 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____148  in
              [uu____147]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____146
             in
          uu____145 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____157 =
            let uu____158 =
              let uu____159 =
                let uu____160 = embed_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____160  in
              let uu____161 =
                let uu____164 =
                  let uu____165 =
                    let uu____166 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern
                       in
                    uu____166 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____165  in
                [uu____164]  in
              uu____159 :: uu____161  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____158
             in
          uu____157 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____177 =
            let uu____178 =
              let uu____179 =
                let uu____180 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____180  in
              [uu____179]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____178
             in
          uu____177 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____184 =
            let uu____185 =
              let uu____186 =
                let uu____187 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____187  in
              [uu____186]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____185
             in
          uu____184 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____192 =
            let uu____193 =
              let uu____194 =
                let uu____195 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____195  in
              let uu____196 =
                let uu____199 =
                  let uu____200 = embed_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____200  in
                [uu____199]  in
              uu____194 :: uu____196  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____193
             in
          uu____192 FStar_Pervasives_Native.None rng
  
let (embed_branch_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Range.range ->
      (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term)
  =
  fun aqs  ->
    fun rng  ->
      fun br  ->
        let uu____220 =
          let uu____227 = embed_term_aq aqs  in
          FStar_Syntax_Embeddings.embed_tuple2 embed_pattern
            FStar_Reflection_Data.fstar_refl_pattern uu____227
            FStar_Syntax_Syntax.t_term
           in
        uu____220 rng br
  
let (embed_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Range.range ->
      (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
        FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term)
  =
  fun aqs  ->
    fun rng  ->
      fun aq  ->
        let uu____256 =
          let uu____263 = embed_term_aq aqs  in
          FStar_Syntax_Embeddings.embed_tuple2 uu____263
            FStar_Syntax_Syntax.t_term embed_aqualv
            FStar_Reflection_Data.fstar_refl_aqualv
           in
        uu____256 rng aq
  
let (embed_branch :
  FStar_Range.range ->
    FStar_Reflection_Data.branch -> FStar_Syntax_Syntax.term)
  = fun rng  -> fun br  -> embed_branch_aq [] rng br 
let (embed_argv :
  FStar_Range.range -> FStar_Reflection_Data.argv -> FStar_Syntax_Syntax.term)
  = fun rng  -> fun aq  -> embed_argv_aq [] rng aq 
let (embed_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedder)
  =
  fun aq  ->
    fun rng  ->
      fun t  ->
        match t with
        | FStar_Reflection_Data.Tv_FVar fv ->
            let uu____323 =
              let uu____324 =
                let uu____325 =
                  let uu____326 = embed_fv rng fv  in
                  FStar_Syntax_Syntax.as_arg uu____326  in
                [uu____325]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
                uu____324
               in
            uu____323 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_BVar fv ->
            let uu____330 =
              let uu____331 =
                let uu____332 =
                  let uu____333 = embed_bv rng fv  in
                  FStar_Syntax_Syntax.as_arg uu____333  in
                [uu____332]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
                uu____331
               in
            uu____330 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_Var bv ->
            let uu____337 =
              let uu____338 =
                let uu____339 =
                  let uu____340 = embed_bv rng bv  in
                  FStar_Syntax_Syntax.as_arg uu____340  in
                [uu____339]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
                uu____338
               in
            uu____337 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_App (hd1,a) ->
            let uu____345 =
              let uu____346 =
                let uu____347 =
                  let uu____348 =
                    let uu____349 = embed_term_aq aq  in uu____349 rng hd1
                     in
                  FStar_Syntax_Syntax.as_arg uu____348  in
                let uu____355 =
                  let uu____358 =
                    let uu____359 = embed_argv_aq aq rng a  in
                    FStar_Syntax_Syntax.as_arg uu____359  in
                  [uu____358]  in
                uu____347 :: uu____355  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
                uu____346
               in
            uu____345 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_Abs (b,t1) ->
            let uu____364 =
              let uu____365 =
                let uu____366 =
                  let uu____367 = embed_binder rng b  in
                  FStar_Syntax_Syntax.as_arg uu____367  in
                let uu____368 =
                  let uu____371 =
                    let uu____372 =
                      let uu____373 = embed_term_aq aq  in uu____373 rng t1
                       in
                    FStar_Syntax_Syntax.as_arg uu____372  in
                  [uu____371]  in
                uu____366 :: uu____368  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
                uu____365
               in
            uu____364 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_Arrow (b,c) ->
            let uu____383 =
              let uu____384 =
                let uu____385 =
                  let uu____386 = embed_binder rng b  in
                  FStar_Syntax_Syntax.as_arg uu____386  in
                let uu____387 =
                  let uu____390 =
                    let uu____391 = embed_comp rng c  in
                    FStar_Syntax_Syntax.as_arg uu____391  in
                  [uu____390]  in
                uu____385 :: uu____387  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
                uu____384
               in
            uu____383 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_Type u ->
            let uu____395 =
              let uu____396 =
                let uu____397 =
                  let uu____398 = FStar_Syntax_Embeddings.embed_unit rng ()
                     in
                  FStar_Syntax_Syntax.as_arg uu____398  in
                [uu____397]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
                uu____396
               in
            uu____395 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
            let uu____403 =
              let uu____404 =
                let uu____405 =
                  let uu____406 = embed_bv rng bv  in
                  FStar_Syntax_Syntax.as_arg uu____406  in
                let uu____407 =
                  let uu____410 =
                    let uu____411 =
                      let uu____412 = embed_term_aq aq  in uu____412 rng t1
                       in
                    FStar_Syntax_Syntax.as_arg uu____411  in
                  [uu____410]  in
                uu____405 :: uu____407  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
                uu____404
               in
            uu____403 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_Const c ->
            let uu____421 =
              let uu____422 =
                let uu____423 =
                  let uu____424 = embed_const rng c  in
                  FStar_Syntax_Syntax.as_arg uu____424  in
                [uu____423]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
                uu____422
               in
            uu____421 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
            let uu____429 =
              let uu____430 =
                let uu____431 =
                  let uu____432 = FStar_Syntax_Embeddings.embed_int rng u  in
                  FStar_Syntax_Syntax.as_arg uu____432  in
                let uu____433 =
                  let uu____436 =
                    let uu____437 =
                      let uu____438 = embed_term_aq aq  in uu____438 rng t1
                       in
                    FStar_Syntax_Syntax.as_arg uu____437  in
                  [uu____436]  in
                uu____431 :: uu____433  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
                uu____430
               in
            uu____429 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
            let uu____450 =
              let uu____451 =
                let uu____452 =
                  let uu____453 = FStar_Syntax_Embeddings.embed_bool rng r
                     in
                  FStar_Syntax_Syntax.as_arg uu____453  in
                let uu____454 =
                  let uu____457 =
                    let uu____458 = embed_bv rng b  in
                    FStar_Syntax_Syntax.as_arg uu____458  in
                  let uu____459 =
                    let uu____462 =
                      let uu____463 =
                        let uu____464 = embed_term_aq aq  in uu____464 rng t1
                         in
                      FStar_Syntax_Syntax.as_arg uu____463  in
                    let uu____470 =
                      let uu____473 =
                        let uu____474 =
                          let uu____475 = embed_term_aq aq  in
                          uu____475 rng t2  in
                        FStar_Syntax_Syntax.as_arg uu____474  in
                      [uu____473]  in
                    uu____462 :: uu____470  in
                  uu____457 :: uu____459  in
                uu____452 :: uu____454  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
                uu____451
               in
            uu____450 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_Match (t1,brs) ->
            let uu____489 =
              let uu____490 =
                let uu____491 =
                  let uu____492 =
                    let uu____493 = embed_term_aq aq  in uu____493 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____492  in
                let uu____499 =
                  let uu____502 =
                    let uu____503 =
                      let uu____504 =
                        FStar_Syntax_Embeddings.embed_list
                          (embed_branch_aq aq)
                          FStar_Reflection_Data.fstar_refl_branch
                         in
                      uu____504 rng brs  in
                    FStar_Syntax_Syntax.as_arg uu____503  in
                  [uu____502]  in
                uu____491 :: uu____499  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
                uu____490
               in
            uu____489 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
            let uu____529 =
              let uu____530 =
                let uu____531 =
                  let uu____532 =
                    let uu____533 = embed_term_aq aq  in uu____533 rng e  in
                  FStar_Syntax_Syntax.as_arg uu____532  in
                let uu____539 =
                  let uu____542 =
                    let uu____543 =
                      let uu____544 = embed_term_aq aq  in uu____544 rng t1
                       in
                    FStar_Syntax_Syntax.as_arg uu____543  in
                  let uu____550 =
                    let uu____553 =
                      let uu____554 =
                        let uu____555 =
                          let uu____560 = embed_term_aq aq  in
                          FStar_Syntax_Embeddings.embed_option uu____560
                            FStar_Reflection_Data.fstar_refl_term
                           in
                        uu____555 rng tacopt  in
                      FStar_Syntax_Syntax.as_arg uu____554  in
                    [uu____553]  in
                  uu____542 :: uu____550  in
                uu____531 :: uu____539  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
                uu____530
               in
            uu____529 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
            let uu____581 =
              let uu____582 =
                let uu____583 =
                  let uu____584 =
                    let uu____585 = embed_term_aq aq  in uu____585 rng e  in
                  FStar_Syntax_Syntax.as_arg uu____584  in
                let uu____591 =
                  let uu____594 =
                    let uu____595 = embed_comp rng c  in
                    FStar_Syntax_Syntax.as_arg uu____595  in
                  let uu____596 =
                    let uu____599 =
                      let uu____600 =
                        let uu____601 =
                          let uu____606 = embed_term_aq aq  in
                          FStar_Syntax_Embeddings.embed_option uu____606
                            FStar_Reflection_Data.fstar_refl_term
                           in
                        uu____601 rng tacopt  in
                      FStar_Syntax_Syntax.as_arg uu____600  in
                    [uu____599]  in
                  uu____594 :: uu____596  in
                uu____583 :: uu____591  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
                uu____582
               in
            uu____581 FStar_Pervasives_Native.None rng
        | FStar_Reflection_Data.Tv_Unknown  ->
            let uu___124_620 =
              FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t
               in
            {
              FStar_Syntax_Syntax.n = (uu___124_620.FStar_Syntax_Syntax.n);
              FStar_Syntax_Syntax.pos = rng;
              FStar_Syntax_Syntax.vars =
                (uu___124_620.FStar_Syntax_Syntax.vars)
            }
  
let (embed_term_view :
  FStar_Range.range ->
    FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  -> let uu____630 = embed_term_view_aq []  in uu____630 rng t
  
let (embed_bv_view :
  FStar_Range.range ->
    FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun bvv  ->
      let uu____653 =
        let uu____654 =
          let uu____655 =
            let uu____656 =
              FStar_Syntax_Embeddings.embed_string rng
                bvv.FStar_Reflection_Data.bv_ppname
               in
            FStar_Syntax_Syntax.as_arg uu____656  in
          let uu____657 =
            let uu____660 =
              let uu____661 =
                FStar_Syntax_Embeddings.embed_int rng
                  bvv.FStar_Reflection_Data.bv_index
                 in
              FStar_Syntax_Syntax.as_arg uu____661  in
            let uu____662 =
              let uu____665 =
                let uu____666 =
                  embed_term rng bvv.FStar_Reflection_Data.bv_sort  in
                FStar_Syntax_Syntax.as_arg uu____666  in
              [uu____665]  in
            uu____660 :: uu____662  in
          uu____655 :: uu____657  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____654
         in
      uu____653 FStar_Pervasives_Native.None rng
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total (t,md) ->
          let uu____684 =
            let uu____685 =
              let uu____686 =
                let uu____687 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____687  in
              let uu____688 =
                let uu____691 =
                  let uu____692 =
                    let uu____693 =
                      FStar_Syntax_Embeddings.embed_option embed_term
                        FStar_Syntax_Syntax.t_term
                       in
                    uu____693 rng md  in
                  FStar_Syntax_Syntax.as_arg uu____692  in
                [uu____691]  in
              uu____686 :: uu____688  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____685
             in
          uu____684 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____708 =
            let uu____709 =
              let uu____710 =
                let uu____711 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____711  in
              let uu____712 =
                let uu____715 =
                  let uu____716 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____716  in
                [uu____715]  in
              uu____710 :: uu____712  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____709
             in
          uu____708 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___125_719 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___125_719.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___125_719.FStar_Syntax_Syntax.vars)
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
      let uu___126_730 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___126_730.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___126_730.FStar_Syntax_Syntax.vars)
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
          let uu____753 =
            let uu____754 =
              let uu____755 =
                let uu____756 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____756  in
              let uu____757 =
                let uu____760 =
                  let uu____761 = embed_fv rng fv  in
                  FStar_Syntax_Syntax.as_arg uu____761  in
                let uu____762 =
                  let uu____765 =
                    let uu____766 = embed_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____766  in
                  let uu____767 =
                    let uu____770 =
                      let uu____771 = embed_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____771  in
                    [uu____770]  in
                  uu____765 :: uu____767  in
                uu____760 :: uu____762  in
              uu____755 :: uu____757  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____754
             in
          uu____753 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
          let uu____776 =
            let uu____777 =
              let uu____778 =
                let uu____779 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____779  in
              let uu____780 =
                let uu____783 =
                  let uu____784 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____784  in
                [uu____783]  in
              uu____778 :: uu____780  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
              uu____777
             in
          uu____776 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____799 =
            let uu____800 =
              let uu____801 =
                let uu____802 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____802  in
              let uu____803 =
                let uu____806 =
                  let uu____807 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____807  in
                let uu____808 =
                  let uu____811 =
                    let uu____812 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____812  in
                  let uu____813 =
                    let uu____816 =
                      let uu____817 =
                        let uu____818 =
                          let uu____825 =
                            FStar_Syntax_Syntax.t_list_of
                              FStar_Syntax_Syntax.t_string
                             in
                          FStar_Syntax_Embeddings.embed_list
                            FStar_Syntax_Embeddings.embed_string_list
                            uu____825
                           in
                        uu____818 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____817  in
                    [uu____816]  in
                  uu____811 :: uu____813  in
                uu____806 :: uu____808  in
              uu____801 :: uu____803  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____800
             in
          uu____799 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___127_833 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___127_833.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___127_833.FStar_Syntax_Syntax.vars)
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
            let uu____843 =
              let uu____844 =
                let uu____845 =
                  let uu____846 =
                    let uu____847 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____847  in
                  FStar_Syntax_Syntax.as_arg uu____846  in
                [uu____845]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
                uu____844
               in
            uu____843 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.Mult (e1,e2) ->
            let uu____852 =
              let uu____853 =
                let uu____854 =
                  let uu____855 = embed_exp rng e1  in
                  FStar_Syntax_Syntax.as_arg uu____855  in
                let uu____856 =
                  let uu____859 =
                    let uu____860 = embed_exp rng e2  in
                    FStar_Syntax_Syntax.as_arg uu____860  in
                  [uu____859]  in
                uu____854 :: uu____856  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
                uu____853
               in
            uu____852 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___128_863 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___128_863.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___128_863.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_bv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____873 =
      let uu____874 = FStar_Syntax_Subst.compress t  in
      uu____874.FStar_Syntax_Syntax.n  in
    match uu____873 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____880 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____880
    | uu____881 ->
        ((let uu____883 =
            let uu____888 =
              let uu____889 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____889  in
            (FStar_Errors.Warning_NotEmbedded, uu____888)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____883);
         FStar_Pervasives_Native.None)
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____899 =
      let uu____900 = FStar_Syntax_Subst.compress t  in
      uu____900.FStar_Syntax_Syntax.n  in
    match uu____899 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____906 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____906
    | uu____907 ->
        ((let uu____909 =
            let uu____914 =
              let uu____915 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____915  in
            (FStar_Errors.Warning_NotEmbedded, uu____914)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____909);
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
          let uu____955 = f x  in
          FStar_Util.bind_opt uu____955
            (fun x1  ->
               let uu____963 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____963
                 (fun xs1  -> FStar_Pervasives_Native.Some (x1 :: xs1)))
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let aqs =
          mapM_opt
            (fun uu____1011  ->
               match uu____1011 with
               | (bv,b,e) ->
                   if b
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.NT (bv, e))
                   else
                     (let uu____1034 = unembed_term e  in
                      FStar_Util.bind_opt uu____1034
                        (fun e1  ->
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.NT (bv, e1)))))
            qi.FStar_Syntax_Syntax.antiquotes
           in
        FStar_Util.bind_opt aqs
          (fun s  ->
             let uu____1046 = FStar_Syntax_Subst.subst s tm  in
             FStar_Pervasives_Native.Some uu____1046)
    | uu____1047 ->
        ((let uu____1049 =
            let uu____1054 =
              let uu____1055 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____1055  in
            (FStar_Errors.Warning_NotEmbedded, uu____1054)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1049);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1066 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1066 with
    | (hd1,args) ->
        let uu____1105 =
          let uu____1118 =
            let uu____1119 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1119.FStar_Syntax_Syntax.n  in
          (uu____1118, args)  in
        (match uu____1105 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____1162 ->
             ((let uu____1176 =
                 let uu____1181 =
                   let uu____1182 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____1182
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1181)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1176);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____1190 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____1190 t
  
let (unembed_fv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____1206 =
      let uu____1207 = FStar_Syntax_Subst.compress t  in
      uu____1207.FStar_Syntax_Syntax.n  in
    match uu____1206 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____1213 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____1213
    | uu____1214 ->
        ((let uu____1216 =
            let uu____1221 =
              let uu____1222 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____1222  in
            (FStar_Errors.Warning_NotEmbedded, uu____1221)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1216);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____1232 =
      let uu____1233 = FStar_Syntax_Subst.compress t  in
      uu____1233.FStar_Syntax_Syntax.n  in
    match uu____1232 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____1239 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____1239
    | uu____1240 ->
        ((let uu____1242 =
            let uu____1247 =
              let uu____1248 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____1248  in
            (FStar_Errors.Warning_NotEmbedded, uu____1247)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1242);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____1258 =
      let uu____1259 = FStar_Syntax_Subst.compress t  in
      uu____1259.FStar_Syntax_Syntax.n  in
    match uu____1258 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____1265 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____1265
    | uu____1266 ->
        ((let uu____1268 =
            let uu____1273 =
              let uu____1274 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____1274  in
            (FStar_Errors.Warning_NotEmbedded, uu____1273)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1268);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1285 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1285 with
    | (hd1,args) ->
        let uu____1324 =
          let uu____1337 =
            let uu____1338 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1338.FStar_Syntax_Syntax.n  in
          (uu____1337, args)  in
        (match uu____1324 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1398)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1423 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____1423
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1432)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1457 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____1457
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1464 ->
             ((let uu____1478 =
                 let uu____1483 =
                   let uu____1484 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____1484
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1483)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1478);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1493 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1493 with
    | (hd1,args) ->
        let uu____1532 =
          let uu____1545 =
            let uu____1546 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1546.FStar_Syntax_Syntax.n  in
          (uu____1545, args)  in
        (match uu____1532 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1561)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1586 = unembed_const c  in
             FStar_Util.bind_opt uu____1586
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1595)::(ps,uu____1597)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1632 = unembed_fv f  in
             FStar_Util.bind_opt uu____1632
               (fun f1  ->
                  let uu____1638 =
                    let uu____1643 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1643 ps  in
                  FStar_Util.bind_opt uu____1638
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1662)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1687 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1687
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var bv1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1696)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1721 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1721
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild bv1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(bv,uu____1730)::(t2,uu____1732)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
             ->
             let uu____1767 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1767
               (fun bv1  ->
                  let uu____1773 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1773
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                         (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
         | uu____1780 ->
             ((let uu____1794 =
                 let uu____1799 =
                   let uu____1800 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1800
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1799)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1794);
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
    let uu____1830 = FStar_Syntax_Util.head_and_args t  in
    match uu____1830 with
    | (hd1,args) ->
        let uu____1869 =
          let uu____1882 =
            let uu____1883 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1883.FStar_Syntax_Syntax.n  in
          (uu____1882, args)  in
        (match uu____1869 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1898)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1923 = unembed_bv b  in
             FStar_Util.bind_opt uu____1923
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1932)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
             ->
             let uu____1957 = unembed_bv b  in
             FStar_Util.bind_opt uu____1957
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                    (FStar_Reflection_Data.Tv_BVar b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1966)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1991 = unembed_fv f  in
             FStar_Util.bind_opt uu____1991
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____2000)::(r,uu____2002)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____2037 = unembed_term l  in
             FStar_Util.bind_opt uu____2037
               (fun l1  ->
                  let uu____2043 = unembed_argv r  in
                  FStar_Util.bind_opt uu____2043
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2068)::(t1,uu____2070)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____2105 = unembed_binder b  in
             FStar_Util.bind_opt uu____2105
               (fun b1  ->
                  let uu____2111 = unembed_term t1  in
                  FStar_Util.bind_opt uu____2111
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                         (FStar_Reflection_Data.Tv_Abs (b1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2120)::(t1,uu____2122)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____2157 = unembed_binder b  in
             FStar_Util.bind_opt uu____2157
               (fun b1  ->
                  let uu____2163 = unembed_comp t1  in
                  FStar_Util.bind_opt uu____2163
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2172)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____2197 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____2197
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2206)::(t1,uu____2208)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____2243 = unembed_bv b  in
             FStar_Util.bind_opt uu____2243
               (fun b1  ->
                  let uu____2249 = unembed_term t1  in
                  FStar_Util.bind_opt uu____2249
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Refine (b1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2258)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____2283 = unembed_const c  in
             FStar_Util.bind_opt uu____2283
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____2292)::(t1,uu____2294)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____2329 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____2329
               (fun u1  ->
                  let uu____2335 = unembed_term t1  in
                  FStar_Util.bind_opt uu____2335
                    (fun t2  ->
                       FStar_All.pipe_left
                         (fun _0_56  -> FStar_Pervasives_Native.Some _0_56)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t2))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____2344)::(b,uu____2346)::(t1,uu____2348)::(t2,uu____2350)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____2405 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____2405
               (fun r1  ->
                  let uu____2411 = unembed_bv b  in
                  FStar_Util.bind_opt uu____2411
                    (fun b1  ->
                       let uu____2417 = unembed_term t1  in
                       FStar_Util.bind_opt uu____2417
                         (fun t11  ->
                            let uu____2423 = unembed_term t2  in
                            FStar_Util.bind_opt uu____2423
                              (fun t21  ->
                                 FStar_All.pipe_left
                                   (fun _0_57  ->
                                      FStar_Pervasives_Native.Some _0_57)
                                   (FStar_Reflection_Data.Tv_Let
                                      (r1, b1, t11, t21))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t1,uu____2432)::(brs,uu____2434)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____2469 = unembed_term t1  in
             FStar_Util.bind_opt uu____2469
               (fun t2  ->
                  let uu____2475 =
                    let uu____2484 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____2484 brs  in
                  FStar_Util.bind_opt uu____2475
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                         (FStar_Reflection_Data.Tv_Match (t2, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e,uu____2523)::(t1,uu____2525)::(tacopt,uu____2527)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
             ->
             let uu____2572 = unembed_term e  in
             FStar_Util.bind_opt uu____2572
               (fun e1  ->
                  let uu____2578 = unembed_term t1  in
                  FStar_Util.bind_opt uu____2578
                    (fun t2  ->
                       let uu____2584 =
                         let uu____2589 =
                           FStar_Syntax_Embeddings.unembed_option
                             unembed_term
                            in
                         uu____2589 tacopt  in
                       FStar_Util.bind_opt uu____2584
                         (fun tacopt1  ->
                            FStar_All.pipe_left
                              (fun _0_59  ->
                                 FStar_Pervasives_Native.Some _0_59)
                              (FStar_Reflection_Data.Tv_AscribedT
                                 (e1, t2, tacopt1)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e,uu____2608)::(c,uu____2610)::(tacopt,uu____2612)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
             ->
             let uu____2657 = unembed_term e  in
             FStar_Util.bind_opt uu____2657
               (fun e1  ->
                  let uu____2663 = unembed_comp c  in
                  FStar_Util.bind_opt uu____2663
                    (fun c1  ->
                       let uu____2669 =
                         let uu____2674 =
                           FStar_Syntax_Embeddings.unembed_option
                             unembed_term
                            in
                         uu____2674 tacopt  in
                       FStar_Util.bind_opt uu____2669
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
         | uu____2708 ->
             ((let uu____2722 =
                 let uu____2727 =
                   let uu____2728 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____2728
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2727)  in
               FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2722);
              FStar_Pervasives_Native.None))
  
let (unembed_bv_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.bv_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2739 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2739 with
    | (hd1,args) ->
        let uu____2778 =
          let uu____2791 =
            let uu____2792 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2792.FStar_Syntax_Syntax.n  in
          (uu____2791, args)  in
        (match uu____2778 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2807)::(idx,uu____2809)::(s,uu____2811)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2856 = FStar_Syntax_Embeddings.unembed_string nm  in
             FStar_Util.bind_opt uu____2856
               (fun nm1  ->
                  let uu____2862 = FStar_Syntax_Embeddings.unembed_int idx
                     in
                  FStar_Util.bind_opt uu____2862
                    (fun idx1  ->
                       let uu____2868 = unembed_term s  in
                       FStar_Util.bind_opt uu____2868
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_62  ->
                                 FStar_Pervasives_Native.Some _0_62)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2875 ->
             ((let uu____2889 =
                 let uu____2894 =
                   let uu____2895 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded bv_view: %s"
                     uu____2895
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2894)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2889);
              FStar_Pervasives_Native.None))
  
let rec (unembed_exp :
  FStar_Reflection_Data.exp FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2904 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2904 with
    | (hd1,args) ->
        let uu____2943 =
          let uu____2956 =
            let uu____2957 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2957.FStar_Syntax_Syntax.n  in
          (uu____2956, args)  in
        (match uu____2943 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____2987)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____3012 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____3012
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_63  -> FStar_Pervasives_Native.Some _0_63)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____3021)::(e2,uu____3023)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____3058 = unembed_exp e1  in
             FStar_Util.bind_opt uu____3058
               (fun e11  ->
                  let uu____3064 = unembed_exp e2  in
                  FStar_Util.bind_opt uu____3064
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____3071 ->
             ((let uu____3085 =
                 let uu____3090 =
                   let uu____3091 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded exp: %s" uu____3091
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3090)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3085);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3102 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3102 with
    | (hd1,args) ->
        let uu____3141 =
          let uu____3154 =
            let uu____3155 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3155.FStar_Syntax_Syntax.n  in
          (uu____3154, args)  in
        (match uu____3141 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____3170)::(md,uu____3172)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____3207 = unembed_term t2  in
             FStar_Util.bind_opt uu____3207
               (fun t3  ->
                  let uu____3213 =
                    let uu____3218 =
                      FStar_Syntax_Embeddings.unembed_option unembed_term  in
                    uu____3218 md  in
                  FStar_Util.bind_opt uu____3213
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_65  -> FStar_Pervasives_Native.Some _0_65)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____3237)::(post,uu____3239)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____3274 = unembed_term pre  in
             FStar_Util.bind_opt uu____3274
               (fun pre1  ->
                  let uu____3280 = unembed_term post  in
                  FStar_Util.bind_opt uu____3280
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
         | uu____3304 ->
             ((let uu____3318 =
                 let uu____3323 =
                   let uu____3324 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____3324
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3323)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3318);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3335 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3335 with
    | (hd1,args) ->
        let uu____3374 =
          let uu____3387 =
            let uu____3388 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3388.FStar_Syntax_Syntax.n  in
          (uu____3387, args)  in
        (match uu____3374 with
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
         | uu____3446 ->
             ((let uu____3460 =
                 let uu____3465 =
                   let uu____3466 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____3466
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3465)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3460);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____3476 =
      let uu____3477 = FStar_Syntax_Subst.compress t  in
      uu____3477.FStar_Syntax_Syntax.n  in
    match uu____3476 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____3483 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____3483
    | uu____3484 ->
        ((let uu____3486 =
            let uu____3491 =
              let uu____3492 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3492  in
            (FStar_Errors.Warning_NotEmbedded, uu____3491)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____3486);
         FStar_Pervasives_Native.None)
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3503 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3503 with
    | (hd1,args) ->
        let uu____3542 =
          let uu____3555 =
            let uu____3556 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3556.FStar_Syntax_Syntax.n  in
          (uu____3555, args)  in
        (match uu____3542 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3571)::(bs,uu____3573)::(t2,uu____3575)::(dcs,uu____3577)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3632 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3632
               (fun nm1  ->
                  let uu____3644 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____3644
                    (fun bs1  ->
                       let uu____3650 = unembed_term t2  in
                       FStar_Util.bind_opt uu____3650
                         (fun t3  ->
                            let uu____3656 =
                              let uu____3663 =
                                let uu____3670 =
                                  FStar_Syntax_Embeddings.unembed_list
                                    FStar_Syntax_Embeddings.unembed_string
                                   in
                                FStar_Syntax_Embeddings.unembed_list
                                  uu____3670
                                 in
                              uu____3663 dcs  in
                            FStar_Util.bind_opt uu____3656
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_Pervasives_Native.Some _0_68)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____3703)::(fvar1,uu____3705)::(ty,uu____3707)::(t2,uu____3709)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____3764 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____3764
               (fun r1  ->
                  let uu____3770 = unembed_fv fvar1  in
                  FStar_Util.bind_opt uu____3770
                    (fun fvar2  ->
                       let uu____3776 = unembed_term ty  in
                       FStar_Util.bind_opt uu____3776
                         (fun ty1  ->
                            let uu____3782 = unembed_term t2  in
                            FStar_Util.bind_opt uu____3782
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
         | uu____3804 ->
             ((let uu____3818 =
                 let uu____3823 =
                   let uu____3824 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____3824
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3823)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3818);
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
    let uu____3851 =
      let uu____3852 =
        let uu____3853 =
          let uu____3854 =
            let uu____3855 = FStar_Reflection_Basic.inspect_bv bv  in
            embed_bv_view i.FStar_Syntax_Syntax.rng uu____3855  in
          FStar_Syntax_Syntax.as_arg uu____3854  in
        [uu____3853]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____3852
       in
    uu____3851 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3862 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____3862 with
    | (bv,aq) ->
        let uu____3869 =
          let uu____3870 =
            let uu____3871 =
              let uu____3872 = embed_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____3872  in
            let uu____3873 =
              let uu____3876 =
                let uu____3877 = embed_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____3877  in
              [uu____3876]  in
            uu____3871 :: uu____3873  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____3870
           in
        uu____3869 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3884 =
      let uu____3885 =
        let uu____3886 =
          let uu____3887 =
            let uu____3888 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____3891 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____3891 i.FStar_Syntax_Syntax.rng uu____3888  in
          FStar_Syntax_Syntax.as_arg uu____3887  in
        [uu____3886]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____3885
       in
    uu____3884 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3905 =
      let uu____3906 =
        let uu____3907 =
          let uu____3908 =
            let uu____3909 = FStar_Reflection_Basic.inspect_comp comp  in
            embed_comp_view i.FStar_Syntax_Syntax.rng uu____3909  in
          FStar_Syntax_Syntax.as_arg uu____3908  in
        [uu____3907]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____3906
       in
    uu____3905 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3919 =
      let uu____3920 =
        let uu____3921 =
          let uu____3922 =
            let uu____3923 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed_sigelt_view i.FStar_Syntax_Syntax.rng uu____3923  in
          FStar_Syntax_Syntax.as_arg uu____3922  in
        [uu____3921]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____3920
       in
    uu____3919 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  