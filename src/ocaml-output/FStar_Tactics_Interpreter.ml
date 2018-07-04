open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec e_tactic_0 :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____255 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____262  ->
         fun uu____263  ->
           fun uu____264  ->
             fun uu____265  -> failwith "Impossible: embedding tactic (0)?")
      (fun t  ->
         fun w  ->
           fun norm1  ->
             let uu____298 = unembed_tactic_0 er t norm1  in
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____298)
      uu____255

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____317 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____327  ->
           fun uu____328  ->
             fun uu____329  ->
               fun uu____330  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  -> fun w  -> unembed_tactic_1 ea er t) uu____317

and e_tactic_nbe_0 :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____368  -> failwith "Impossible: NBE embedding tactic (0)?")
      (fun cb  ->
         fun t  ->
           let uu____384 = unembed_tactic_nbe_0 er cb t  in
           FStar_All.pipe_left
             (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____384)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)

and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____413  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  -> fun t  -> unembed_tactic_nbe_1 ea er cb t)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____434  ->
    let tracepoint1 =
      let uu___349_438 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____439 = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____439;
        FStar_TypeChecker_Cfg.arity =
          (uu___349_438.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___349_438.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___349_438.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___349_438.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___349_438.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___349_438.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___349_438.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let set_proofstate_range1 =
      let uu___350_441 =
        FStar_Tactics_InterpFuns.mktot2 (Prims.parse_int "0")
          "set_proofstate_range" FStar_Tactics_Types.set_proofstate_range
          FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_range
          FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Types.set_proofstate_range
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_range
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____442 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Cfg.name = uu____442;
        FStar_TypeChecker_Cfg.arity =
          (uu___350_441.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___350_441.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___350_441.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___350_441.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___350_441.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___350_441.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___350_441.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let incr_depth1 =
      let uu___351_444 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "incr_depth"
          FStar_Tactics_Types.incr_depth FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.incr_depth
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____445 = FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____445;
        FStar_TypeChecker_Cfg.arity =
          (uu___351_444.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___351_444.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___351_444.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___351_444.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___351_444.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___351_444.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___351_444.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let decr_depth1 =
      let uu___352_447 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "decr_depth"
          FStar_Tactics_Types.decr_depth FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.decr_depth
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____448 = FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____448;
        FStar_TypeChecker_Cfg.arity =
          (uu___352_447.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___352_447.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___352_447.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___352_447.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___352_447.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___352_447.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___352_447.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let uu____449 =
      let uu____452 =
        let uu____455 =
          let uu____458 =
            let uu____461 =
              let uu____464 =
                FStar_Tactics_InterpFuns.mktot2 (Prims.parse_int "0")
                  "push_binder"
                  (fun env  ->
                     fun b  -> FStar_TypeChecker_Env.push_binders env [b])
                  FStar_Reflection_Embeddings.e_env
                  FStar_Reflection_Embeddings.e_binder
                  FStar_Reflection_Embeddings.e_env
                  (fun env  ->
                     fun b  -> FStar_TypeChecker_Env.push_binders env [b])
                  FStar_Reflection_NBEEmbeddings.e_env
                  FStar_Reflection_NBEEmbeddings.e_binder
                  FStar_Reflection_NBEEmbeddings.e_env
                 in
              let uu____521 =
                let uu____524 =
                  FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                    "fail" (fun uu____526  -> FStar_Tactics_Basic.fail)
                    FStar_Syntax_Embeddings.e_any
                    FStar_Syntax_Embeddings.e_string
                    FStar_Syntax_Embeddings.e_any
                    (fun uu____528  -> FStar_Tactics_Basic.fail)
                    FStar_TypeChecker_NBETerm.e_any
                    FStar_TypeChecker_NBETerm.e_string
                    FStar_TypeChecker_NBETerm.e_any
                   in
                let uu____529 =
                  let uu____532 =
                    FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                      "trivial" FStar_Tactics_Basic.trivial
                      FStar_Syntax_Embeddings.e_unit
                      FStar_Syntax_Embeddings.e_unit
                      FStar_Tactics_Basic.trivial
                      FStar_TypeChecker_NBETerm.e_unit
                      FStar_TypeChecker_NBETerm.e_unit
                     in
                  let uu____533 =
                    let uu____536 =
                      let uu____537 =
                        e_tactic_0 FStar_Syntax_Embeddings.e_any  in
                      let uu____542 =
                        FStar_Syntax_Embeddings.e_option
                          FStar_Syntax_Embeddings.e_any
                         in
                      let uu____547 =
                        e_tactic_nbe_0 FStar_TypeChecker_NBETerm.e_any  in
                      let uu____552 =
                        FStar_TypeChecker_NBETerm.e_option
                          FStar_TypeChecker_NBETerm.e_any
                         in
                      FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                        "__trytac"
                        (fun uu____566  -> FStar_Tactics_Basic.trytac)
                        FStar_Syntax_Embeddings.e_any uu____537 uu____542
                        (fun uu____568  -> FStar_Tactics_Basic.trytac)
                        FStar_TypeChecker_NBETerm.e_any uu____547 uu____552
                       in
                    let uu____569 =
                      let uu____572 =
                        FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                          "intro" FStar_Tactics_Basic.intro
                          FStar_Syntax_Embeddings.e_unit
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Tactics_Basic.intro
                          FStar_TypeChecker_NBETerm.e_unit
                          FStar_Reflection_NBEEmbeddings.e_binder
                         in
                      let uu____573 =
                        let uu____576 =
                          let uu____577 =
                            FStar_Syntax_Embeddings.e_tuple2
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder
                             in
                          let uu____584 =
                            FStar_TypeChecker_NBETerm.e_tuple2
                              FStar_Reflection_NBEEmbeddings.e_binder
                              FStar_Reflection_NBEEmbeddings.e_binder
                             in
                          FStar_Tactics_InterpFuns.mktac1
                            (Prims.parse_int "0") "intro_rec"
                            FStar_Tactics_Basic.intro_rec
                            FStar_Syntax_Embeddings.e_unit uu____577
                            FStar_Tactics_Basic.intro_rec
                            FStar_TypeChecker_NBETerm.e_unit uu____584
                           in
                        let uu____599 =
                          let uu____602 =
                            let uu____603 =
                              FStar_Syntax_Embeddings.e_list
                                FStar_Syntax_Embeddings.e_norm_step
                               in
                            let uu____608 =
                              FStar_TypeChecker_NBETerm.e_list
                                FStar_TypeChecker_NBETerm.e_norm_step
                               in
                            FStar_Tactics_InterpFuns.mktac1
                              (Prims.parse_int "0") "norm"
                              FStar_Tactics_Basic.norm uu____603
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Tactics_Basic.norm uu____608
                              FStar_TypeChecker_NBETerm.e_unit
                             in
                          let uu____617 =
                            let uu____620 =
                              let uu____621 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_norm_step
                                 in
                              let uu____626 =
                                FStar_TypeChecker_NBETerm.e_list
                                  FStar_TypeChecker_NBETerm.e_norm_step
                                 in
                              FStar_Tactics_InterpFuns.mktac3
                                (Prims.parse_int "0") "norm_term_env"
                                FStar_Tactics_Basic.norm_term_env
                                FStar_Reflection_Embeddings.e_env uu____621
                                FStar_Reflection_Embeddings.e_term
                                FStar_Reflection_Embeddings.e_term
                                FStar_Tactics_Basic.norm_term_env
                                FStar_Reflection_NBEEmbeddings.e_env
                                uu____626
                                FStar_Reflection_NBEEmbeddings.e_term
                                FStar_Reflection_NBEEmbeddings.e_term
                               in
                            let uu____635 =
                              let uu____638 =
                                let uu____639 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Syntax_Embeddings.e_norm_step
                                   in
                                let uu____644 =
                                  FStar_TypeChecker_NBETerm.e_list
                                    FStar_TypeChecker_NBETerm.e_norm_step
                                   in
                                FStar_Tactics_InterpFuns.mktac2
                                  (Prims.parse_int "0") "norm_binder_type"
                                  FStar_Tactics_Basic.norm_binder_type
                                  uu____639
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Tactics_Basic.norm_binder_type
                                  uu____644
                                  FStar_Reflection_NBEEmbeddings.e_binder
                                  FStar_TypeChecker_NBETerm.e_unit
                                 in
                              let uu____653 =
                                let uu____656 =
                                  FStar_Tactics_InterpFuns.mktac2
                                    (Prims.parse_int "0") "rename_to"
                                    FStar_Tactics_Basic.rename_to
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_string
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Basic.rename_to
                                    FStar_Reflection_NBEEmbeddings.e_binder
                                    FStar_TypeChecker_NBETerm.e_string
                                    FStar_TypeChecker_NBETerm.e_unit
                                   in
                                let uu____657 =
                                  let uu____660 =
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "binder_retype"
                                      FStar_Tactics_Basic.binder_retype
                                      FStar_Reflection_Embeddings.e_binder
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.binder_retype
                                      FStar_Reflection_NBEEmbeddings.e_binder
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____661 =
                                    let uu____664 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        (Prims.parse_int "0") "revert"
                                        FStar_Tactics_Basic.revert
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.revert
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____665 =
                                      let uu____668 =
                                        FStar_Tactics_InterpFuns.mktac1
                                          (Prims.parse_int "0") "clear_top"
                                          FStar_Tactics_Basic.clear_top
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Tactics_Basic.clear_top
                                          FStar_TypeChecker_NBETerm.e_unit
                                          FStar_TypeChecker_NBETerm.e_unit
                                         in
                                      let uu____669 =
                                        let uu____672 =
                                          FStar_Tactics_InterpFuns.mktac1
                                            (Prims.parse_int "0") "clear"
                                            FStar_Tactics_Basic.clear
                                            FStar_Reflection_Embeddings.e_binder
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_Tactics_Basic.clear
                                            FStar_Reflection_NBEEmbeddings.e_binder
                                            FStar_TypeChecker_NBETerm.e_unit
                                           in
                                        let uu____673 =
                                          let uu____676 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              (Prims.parse_int "0") "rewrite"
                                              FStar_Tactics_Basic.rewrite
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Tactics_Basic.rewrite
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                              FStar_TypeChecker_NBETerm.e_unit
                                             in
                                          let uu____677 =
                                            let uu____680 =
                                              FStar_Tactics_InterpFuns.mktac1
                                                (Prims.parse_int "0") "smt"
                                                FStar_Tactics_Basic.smt
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Tactics_Basic.smt
                                                FStar_TypeChecker_NBETerm.e_unit
                                                FStar_TypeChecker_NBETerm.e_unit
                                               in
                                            let uu____681 =
                                              let uu____684 =
                                                FStar_Tactics_InterpFuns.mktac1
                                                  (Prims.parse_int "0")
                                                  "refine_intro"
                                                  FStar_Tactics_Basic.refine_intro
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.refine_intro
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                 in
                                              let uu____685 =
                                                let uu____688 =
                                                  FStar_Tactics_InterpFuns.mktac2
                                                    (Prims.parse_int "0")
                                                    "t_exact"
                                                    FStar_Tactics_Basic.t_exact
                                                    FStar_Syntax_Embeddings.e_bool
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Tactics_Basic.t_exact
                                                    FStar_TypeChecker_NBETerm.e_bool
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                    FStar_TypeChecker_NBETerm.e_unit
                                                   in
                                                let uu____689 =
                                                  let uu____692 =
                                                    FStar_Tactics_InterpFuns.mktac1
                                                      (Prims.parse_int "0")
                                                      "apply"
                                                      (FStar_Tactics_Basic.apply
                                                         true)
                                                      FStar_Reflection_Embeddings.e_term
                                                      FStar_Syntax_Embeddings.e_unit
                                                      (FStar_Tactics_Basic.apply
                                                         true)
                                                      FStar_Reflection_NBEEmbeddings.e_term
                                                      FStar_TypeChecker_NBETerm.e_unit
                                                     in
                                                  let uu____693 =
                                                    let uu____696 =
                                                      FStar_Tactics_InterpFuns.mktac1
                                                        (Prims.parse_int "0")
                                                        "apply_raw"
                                                        (FStar_Tactics_Basic.apply
                                                           false)
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Syntax_Embeddings.e_unit
                                                        (FStar_Tactics_Basic.apply
                                                           false)
                                                        FStar_Reflection_NBEEmbeddings.e_term
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                       in
                                                    let uu____697 =
                                                      let uu____700 =
                                                        FStar_Tactics_InterpFuns.mktac1
                                                          (Prims.parse_int "0")
                                                          "apply_lemma"
                                                          FStar_Tactics_Basic.apply_lemma
                                                          FStar_Reflection_Embeddings.e_term
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_Basic.apply_lemma
                                                          FStar_Reflection_NBEEmbeddings.e_term
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                         in
                                                      let uu____701 =
                                                        let uu____704 =
                                                          let uu____705 =
                                                            e_tactic_0
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____710 =
                                                            e_tactic_0
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____715 =
                                                            FStar_Syntax_Embeddings.e_tuple2
                                                              FStar_Syntax_Embeddings.e_any
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____722 =
                                                            e_tactic_nbe_0
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          let uu____727 =
                                                            e_tactic_nbe_0
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          let uu____732 =
                                                            FStar_TypeChecker_NBETerm.e_tuple2
                                                              FStar_TypeChecker_NBETerm.e_any
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          FStar_Tactics_InterpFuns.mktac5
                                                            (Prims.parse_int "2")
                                                            "__divide"
                                                            (fun uu____757 
                                                               ->
                                                               fun uu____758 
                                                                 ->
                                                                 FStar_Tactics_Basic.divide)
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Syntax_Embeddings.e_int
                                                            uu____705
                                                            uu____710
                                                            uu____715
                                                            (fun uu____761 
                                                               ->
                                                               fun uu____762 
                                                                 ->
                                                                 FStar_Tactics_Basic.divide)
                                                            FStar_TypeChecker_NBETerm.e_any
                                                            FStar_TypeChecker_NBETerm.e_any
                                                            FStar_TypeChecker_NBETerm.e_int
                                                            uu____722
                                                            uu____727
                                                            uu____732
                                                           in
                                                        let uu____763 =
                                                          let uu____766 =
                                                            let uu____767 =
                                                              e_tactic_0
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____772 =
                                                              e_tactic_0
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____777 =
                                                              e_tactic_nbe_0
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            let uu____782 =
                                                              e_tactic_nbe_0
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            FStar_Tactics_InterpFuns.mktac2
                                                              (Prims.parse_int "0")
                                                              "__seq"
                                                              FStar_Tactics_Basic.seq
                                                              uu____767
                                                              uu____772
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.seq
                                                              uu____777
                                                              uu____782
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                             in
                                                          let uu____795 =
                                                            let uu____798 =
                                                              FStar_Tactics_InterpFuns.mktac1
                                                                (Prims.parse_int "0")
                                                                "set_options"
                                                                FStar_Tactics_Basic.set_options
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_Basic.set_options
                                                                FStar_TypeChecker_NBETerm.e_string
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            let uu____799 =
                                                              let uu____802 =
                                                                FStar_Tactics_InterpFuns.mktac1
                                                                  (Prims.parse_int "0")
                                                                  "tc"
                                                                  FStar_Tactics_Basic.tc
                                                                  FStar_Reflection_Embeddings.e_term
                                                                  FStar_Reflection_Embeddings.e_term
                                                                  FStar_Tactics_Basic.tc
                                                                  FStar_Reflection_NBEEmbeddings.e_term
                                                                  FStar_Reflection_NBEEmbeddings.e_term
                                                                 in
                                                              let uu____803 =
                                                                let uu____806
                                                                  =
                                                                  FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "unshelve"
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                   in
                                                                let uu____807
                                                                  =
                                                                  let uu____810
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____813
                                                                     ->
                                                                    fun
                                                                    uu____814
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                  let uu____817
                                                                    =
                                                                    let uu____820
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "prune"
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____821
                                                                    =
                                                                    let uu____824
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "addns"
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____825
                                                                    =
                                                                    let uu____828
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "print"
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____829
                                                                    =
                                                                    let uu____832
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "debug"
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____833
                                                                    =
                                                                    let uu____836
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____837
                                                                    =
                                                                    let uu____840
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____841
                                                                    =
                                                                    let uu____844
                                                                    =
                                                                    let uu____845
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____850
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____845
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____850
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____859
                                                                    =
                                                                    let uu____862
                                                                    =
                                                                    let uu____863
                                                                    =
                                                                    let uu____875
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____875
                                                                     in
                                                                    let uu____886
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____891
                                                                    =
                                                                    let uu____903
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____903
                                                                     in
                                                                    let uu____914
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____863
                                                                    uu____886
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____891
                                                                    uu____914
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____941
                                                                    =
                                                                    let uu____944
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____945
                                                                    =
                                                                    let uu____948
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____949
                                                                    =
                                                                    let uu____952
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____953
                                                                    =
                                                                    let uu____956
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____957
                                                                    =
                                                                    let uu____960
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____961
                                                                    =
                                                                    let uu____964
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dismiss"
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____965
                                                                    =
                                                                    let uu____968
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "tadmit"
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____969
                                                                    =
                                                                    let uu____972
                                                                    =
                                                                    let uu____973
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____980
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____973
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____980
                                                                     in
                                                                    let uu____995
                                                                    =
                                                                    let uu____998
                                                                    =
                                                                    let uu____999
                                                                    =
                                                                    let uu____1008
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1008
                                                                     in
                                                                    let uu____1019
                                                                    =
                                                                    let uu____1028
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1028
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____999
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1019
                                                                     in
                                                                    let uu____1051
                                                                    =
                                                                    let uu____1054
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                     in
                                                                    let uu____1055
                                                                    =
                                                                    let uu____1058
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                     in
                                                                    let uu____1059
                                                                    =
                                                                    let uu____1062
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1063
                                                                    =
                                                                    let uu____1066
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1067
                                                                    =
                                                                    let uu____1070
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                     in
                                                                    let uu____1071
                                                                    =
                                                                    let uu____1074
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1075
                                                                    =
                                                                    let uu____1078
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    let uu____1079
                                                                    =
                                                                    let uu____1082
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "ngoals"
                                                                    FStar_Tactics_Basic.ngoals
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.ngoals
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    let uu____1083
                                                                    =
                                                                    let uu____1086
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "ngoals_smt"
                                                                    FStar_Tactics_Basic.ngoals_smt
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.ngoals_smt
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    let uu____1087
                                                                    =
                                                                    let uu____1090
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1091
                                                                    =
                                                                    let uu____1094
                                                                    =
                                                                    let uu____1095
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1100
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1095
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1100
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1109
                                                                    =
                                                                    let uu____1112
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "unify_env"
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1113
                                                                    =
                                                                    let uu____1116
                                                                    =
                                                                    let uu____1117
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1122
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1117
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1122
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1131
                                                                    =
                                                                    let uu____1134
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_bv
                                                                     in
                                                                    let uu____1135
                                                                    =
                                                                    let uu____1138
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1139
                                                                    =
                                                                    let uu____1142
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                     in
                                                                    let uu____1143
                                                                    =
                                                                    let uu____1146
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1147
                                                                    =
                                                                    let uu____1150
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "lax_on"
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    [uu____1150]
                                                                     in
                                                                    uu____1146
                                                                    ::
                                                                    uu____1147
                                                                     in
                                                                    uu____1142
                                                                    ::
                                                                    uu____1143
                                                                     in
                                                                    uu____1138
                                                                    ::
                                                                    uu____1139
                                                                     in
                                                                    uu____1134
                                                                    ::
                                                                    uu____1135
                                                                     in
                                                                    uu____1116
                                                                    ::
                                                                    uu____1131
                                                                     in
                                                                    uu____1112
                                                                    ::
                                                                    uu____1113
                                                                     in
                                                                    uu____1094
                                                                    ::
                                                                    uu____1109
                                                                     in
                                                                    uu____1090
                                                                    ::
                                                                    uu____1091
                                                                     in
                                                                    uu____1086
                                                                    ::
                                                                    uu____1087
                                                                     in
                                                                    uu____1082
                                                                    ::
                                                                    uu____1083
                                                                     in
                                                                    uu____1078
                                                                    ::
                                                                    uu____1079
                                                                     in
                                                                    uu____1074
                                                                    ::
                                                                    uu____1075
                                                                     in
                                                                    uu____1070
                                                                    ::
                                                                    uu____1071
                                                                     in
                                                                    uu____1066
                                                                    ::
                                                                    uu____1067
                                                                     in
                                                                    uu____1062
                                                                    ::
                                                                    uu____1063
                                                                     in
                                                                    uu____1058
                                                                    ::
                                                                    uu____1059
                                                                     in
                                                                    uu____1054
                                                                    ::
                                                                    uu____1055
                                                                     in
                                                                    uu____998
                                                                    ::
                                                                    uu____1051
                                                                     in
                                                                    uu____972
                                                                    ::
                                                                    uu____995
                                                                     in
                                                                    uu____968
                                                                    ::
                                                                    uu____969
                                                                     in
                                                                    uu____964
                                                                    ::
                                                                    uu____965
                                                                     in
                                                                    uu____960
                                                                    ::
                                                                    uu____961
                                                                     in
                                                                    uu____956
                                                                    ::
                                                                    uu____957
                                                                     in
                                                                    uu____952
                                                                    ::
                                                                    uu____953
                                                                     in
                                                                    uu____948
                                                                    ::
                                                                    uu____949
                                                                     in
                                                                    uu____944
                                                                    ::
                                                                    uu____945
                                                                     in
                                                                    uu____862
                                                                    ::
                                                                    uu____941
                                                                     in
                                                                    uu____844
                                                                    ::
                                                                    uu____859
                                                                     in
                                                                    uu____840
                                                                    ::
                                                                    uu____841
                                                                     in
                                                                    uu____836
                                                                    ::
                                                                    uu____837
                                                                     in
                                                                    uu____832
                                                                    ::
                                                                    uu____833
                                                                     in
                                                                    uu____828
                                                                    ::
                                                                    uu____829
                                                                     in
                                                                    uu____824
                                                                    ::
                                                                    uu____825
                                                                     in
                                                                    uu____820
                                                                    ::
                                                                    uu____821
                                                                     in
                                                                  uu____810
                                                                    ::
                                                                    uu____817
                                                                   in
                                                                uu____806 ::
                                                                  uu____807
                                                                 in
                                                              uu____802 ::
                                                                uu____803
                                                               in
                                                            uu____798 ::
                                                              uu____799
                                                             in
                                                          uu____766 ::
                                                            uu____795
                                                           in
                                                        uu____704 ::
                                                          uu____763
                                                         in
                                                      uu____700 :: uu____701
                                                       in
                                                    uu____696 :: uu____697
                                                     in
                                                  uu____692 :: uu____693  in
                                                uu____688 :: uu____689  in
                                              uu____684 :: uu____685  in
                                            uu____680 :: uu____681  in
                                          uu____676 :: uu____677  in
                                        uu____672 :: uu____673  in
                                      uu____668 :: uu____669  in
                                    uu____664 :: uu____665  in
                                  uu____660 :: uu____661  in
                                uu____656 :: uu____657  in
                              uu____638 :: uu____653  in
                            uu____620 :: uu____635  in
                          uu____602 :: uu____617  in
                        uu____576 :: uu____599  in
                      uu____572 :: uu____573  in
                    uu____536 :: uu____569  in
                  uu____532 :: uu____533  in
                uu____524 :: uu____529  in
              uu____464 :: uu____521  in
            set_proofstate_range1 :: uu____461  in
          tracepoint1 :: uu____458  in
        decr_depth1 :: uu____455  in
      incr_depth1 :: uu____452  in
    FStar_List.append uu____449
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         FStar_Tactics_InterpFuns.native_tactics_steps)

and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            ('Aa -> 'Ar FStar_Tactics_Basic.tac)
              FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          FStar_Pervasives_Native.Some
            (fun x  ->
               let rng = FStar_Range.dummyRange  in
               let x_tm = FStar_Tactics_InterpFuns.embed ea rng x ncb  in
               let app =
                 let uu____1178 =
                   let uu____1183 =
                     let uu____1184 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____1184]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1183  in
                 uu____1178 FStar_Pervasives_Native.None rng  in
               unembed_tactic_0 er app ncb)

and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun embedded_tac_b  ->
      fun ncb  ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state  ->
             let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
             let tm =
               let uu____1237 =
                 let uu____1242 =
                   let uu____1243 =
                     let uu____1252 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1252  in
                   [uu____1243]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1242  in
               uu____1237 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1297 = FStar_Options.tactics_nbe ()  in
               if uu____1297
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____1316 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____1316)
             else ();
             (let result =
                let uu____1319 = primitive_steps ()  in
                norm_f uu____1319 steps
                  proof_state.FStar_Tactics_Types.main_context tm
                 in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____1323 = FStar_Syntax_Print.term_to_string result
                    in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____1323)
              else ();
              (let res =
                 let uu____1330 = FStar_Tactics_Embedding.e_result eb  in
                 FStar_Tactics_InterpFuns.unembed uu____1330 result ncb  in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b,ps)) ->
                   let uu____1345 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1345
                     (fun uu____1349  -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (msg,ps)) ->
                   let uu____1354 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1354
                     (fun uu____1358  -> FStar_Tactics_Basic.fail msg)
               | FStar_Pervasives_Native.None  ->
                   let uu____1361 =
                     let uu____1366 =
                       let uu____1367 =
                         FStar_Syntax_Print.term_to_string result  in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____1367
                        in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____1366)  in
                   FStar_Errors.raise_error uu____1361
                     (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.iapp_cb ->
          FStar_TypeChecker_NBETerm.t ->
            ('Aa -> 'Ar FStar_Tactics_Basic.tac)
              FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun cb  ->
        fun f  ->
          FStar_Pervasives_Native.Some
            (fun x  ->
               let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x  in
               let app =
                 let uu____1397 =
                   let uu____1398 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                   [uu____1398]  in
                 cb f uu____1397  in
               unembed_tactic_nbe_0 er cb app)

and unembed_tactic_nbe_0 :
  'Ab .
    'Ab FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.iapp_cb ->
        FStar_TypeChecker_NBETerm.t -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun cb  ->
      fun embedded_tac_b  ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state  ->
             let result =
               let uu____1434 =
                 let uu____1435 =
                   let uu____1440 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1440  in
                 [uu____1435]  in
               cb embedded_tac_b uu____1434  in
             let res =
               let uu____1460 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1460 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1477 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1477
                   (fun uu____1481  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____1486 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1486
                   (fun uu____1490  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____1493 =
                   let uu____1498 =
                     let uu____1499 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1499
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1498)  in
                 FStar_Errors.raise_error uu____1493
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

let report_implicits :
  'Auu____1508 . 'Auu____1508 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____1537 =
               let uu____1538 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____1539 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____1538 uu____1539 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____1537, (imp.FStar_TypeChecker_Env.imp_range))) is
         in
      FStar_Errors.add_errors errs
  
let (run_tactic_on_typ :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.typ ->
            (FStar_Tactics_Basic.goal Prims.list,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2)
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun typ  ->
            (let uu____1578 = FStar_ST.op_Bang tacdbg  in
             if uu____1578
             then
               let uu____1598 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____1598
             else ());
            (let uu____1600 =
               FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic  in
             match uu____1600 with
             | (uu____1613,uu____1614,g) ->
                 ((let uu____1617 = FStar_ST.op_Bang tacdbg  in
                   if uu____1617 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb
                      in
                   let uu____1643 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____1643 with
                   | (env1,uu____1657) ->
                       let env2 =
                         let uu___353_1663 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___353_1663.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___353_1663.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___353_1663.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___353_1663.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___353_1663.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___353_1663.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___353_1663.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___353_1663.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___353_1663.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___353_1663.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___353_1663.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___353_1663.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___353_1663.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___353_1663.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___353_1663.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___353_1663.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___353_1663.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___353_1663.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___353_1663.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___353_1663.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___353_1663.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___353_1663.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___353_1663.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___353_1663.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___353_1663.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___353_1663.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___353_1663.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___353_1663.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___353_1663.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___353_1663.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___353_1663.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___353_1663.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___353_1663.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___353_1663.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___353_1663.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___353_1663.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___353_1663.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___353_1663.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___353_1663.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___353_1663.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___353_1663.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___354_1665 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___354_1665.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___354_1665.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___354_1665.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___354_1665.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___354_1665.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___354_1665.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___354_1665.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___354_1665.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___354_1665.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___354_1665.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___354_1665.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___354_1665.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___354_1665.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___354_1665.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___354_1665.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___354_1665.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___354_1665.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___354_1665.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___354_1665.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___354_1665.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___354_1665.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___354_1665.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___354_1665.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___354_1665.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___354_1665.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___354_1665.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___354_1665.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___354_1665.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___354_1665.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___354_1665.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___354_1665.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___354_1665.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___354_1665.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___354_1665.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___354_1665.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___354_1665.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___354_1665.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___354_1665.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___354_1665.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___354_1665.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___354_1665.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___355_1667 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___355_1667.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___355_1667.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___355_1667.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___355_1667.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___355_1667.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___355_1667.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___355_1667.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___355_1667.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___355_1667.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___355_1667.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___355_1667.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___355_1667.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___355_1667.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___355_1667.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___355_1667.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___355_1667.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___355_1667.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___355_1667.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___355_1667.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___355_1667.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___355_1667.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___355_1667.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___355_1667.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___355_1667.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___355_1667.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___355_1667.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___355_1667.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___355_1667.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___355_1667.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___355_1667.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___355_1667.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___355_1667.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___355_1667.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___355_1667.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___355_1667.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___355_1667.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___355_1667.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___355_1667.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___355_1667.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___355_1667.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___355_1667.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____1669 = FStar_Range.use_range rng_goal  in
                         let uu____1670 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____1669 uu____1670  in
                       let uu____1671 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____1671 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____1709 = FStar_ST.op_Bang tacdbg  in
                              if uu____1709
                              then
                                let uu____1729 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____1729
                              else ());
                             (let uu____1731 =
                                FStar_Util.record_time
                                  (fun uu____1741  ->
                                     FStar_Tactics_Basic.run_safe tau ps)
                                 in
                              match uu____1731 with
                              | (res,ms) ->
                                  ((let uu____1755 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____1755
                                    then
                                      let uu____1775 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____1776 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____1777 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "}\nTactic %s ran in %s ms (%s)\n"
                                        uu____1775 uu____1776 uu____1777
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____1785,ps1) ->
                                        ((let uu____1788 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1788
                                          then
                                            let uu____1808 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____1808
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____1815 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____1815
                                              then
                                                let uu____1816 =
                                                  let uu____1817 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____1818 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt
                                                    uu____1817 uu____1818
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____1816
                                                 then ()
                                                 else
                                                   (let uu____1820 =
                                                      let uu____1821 =
                                                        let uu____1822 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____1822
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____1821
                                                       in
                                                    failwith uu____1820))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____1825 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1825
                                          then
                                            let uu____1845 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____1845
                                          else ());
                                         (let g1 =
                                            let uu___356_1850 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___356_1850.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___356_1850.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___356_1850.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____1853 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____1853
                                           then
                                             let uu____1873 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits)
                                                in
                                             let uu____1874 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____1873 uu____1874
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____1880 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____1880
                                            then
                                              let uu____1900 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits)
                                                 in
                                              let uu____1901 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____1900 uu____1901
                                            else ());
                                           report_implicits ps1
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____1907 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____1907
                                            then
                                              let uu____1927 =
                                                let uu____1928 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc
                                                   in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____1928 ps1
                                                 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____1927
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____1935 =
                                            let uu____1936 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____1936 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____1935
                                            "at the time of failure");
                                         (let uu____1937 =
                                            let uu____1942 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____1942)
                                             in
                                          FStar_Errors.raise_error uu____1937
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____1954 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____1960 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____1966 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2021 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2061 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2115 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____2156 . 'Auu____2156 -> 'Auu____2156 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____2184 = FStar_Syntax_Util.head_and_args t  in
        match uu____2184 with
        | (hd1,args) ->
            let uu____2227 =
              let uu____2242 =
                let uu____2243 = FStar_Syntax_Util.un_uinst hd1  in
                uu____2243.FStar_Syntax_Syntax.n  in
              (uu____2242, args)  in
            (match uu____2227 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2258))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2321 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2321 with
                       | (gs,uu____2329) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____2336 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2336 with
                       | (gs,uu____2344) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2387 =
                        let uu____2394 =
                          let uu____2397 =
                            let uu____2398 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2398
                             in
                          [uu____2397]  in
                        (FStar_Syntax_Util.t_true, uu____2394)  in
                      Simplified uu____2387
                  | Both  ->
                      let uu____2409 =
                        let uu____2418 =
                          let uu____2421 =
                            let uu____2422 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2422
                             in
                          [uu____2421]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____2418)  in
                      Dual uu____2409
                  | Neg  -> Simplified (assertion, []))
             | uu____2435 -> Unchanged t)
  
let explode :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___348_2525  ->
      match uu___348_2525 with
      | Unchanged t -> let uu____2531 = f t  in Unchanged uu____2531
      | Simplified (t,gs) ->
          let uu____2538 = let uu____2545 = f t  in (uu____2545, gs)  in
          Simplified uu____2538
      | Dual (tn,tp,gs) ->
          let uu____2555 =
            let uu____2564 = f tn  in
            let uu____2565 = f tp  in (uu____2564, uu____2565, gs)  in
          Dual uu____2555
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____2628 = f t1 t2  in Unchanged uu____2628
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____2640 = let uu____2647 = f t1 t2  in (uu____2647, gs)
               in
            Simplified uu____2640
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____2661 = let uu____2668 = f t1 t2  in (uu____2668, gs)
               in
            Simplified uu____2661
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____2687 =
              let uu____2694 = f t1 t2  in
              (uu____2694, (FStar_List.append gs1 gs2))  in
            Simplified uu____2687
        | uu____2697 ->
            let uu____2706 = explode x  in
            (match uu____2706 with
             | (n1,p1,gs1) ->
                 let uu____2724 = explode y  in
                 (match uu____2724 with
                  | (n2,p2,gs2) ->
                      let uu____2742 =
                        let uu____2751 = f n1 n2  in
                        let uu____2752 = f p1 p2  in
                        (uu____2751, uu____2752, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____2742))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____2824 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____2824
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____2872  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____2914 =
              let uu____2915 = FStar_Syntax_Subst.compress t  in
              uu____2915.FStar_Syntax_Syntax.n  in
            match uu____2914 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____2927 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____2927 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____2953 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____2953 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2973;
                   FStar_Syntax_Syntax.vars = uu____2974;_},(p,uu____2976)::
                 (q,uu____2978)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3034 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3034
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3037 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3037 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3051 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3051.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3055;
                   FStar_Syntax_Syntax.vars = uu____3056;_},(p,uu____3058)::
                 (q,uu____3060)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3116 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3116
                   in
                let xq =
                  let uu____3118 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3118
                   in
                let r1 =
                  let uu____3120 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3120 p  in
                let r2 =
                  let uu____3122 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3122 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3129,Unchanged uu____3130) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3148 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3148.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3151 ->
                     let uu____3160 = explode r1  in
                     (match uu____3160 with
                      | (pn,pp,gs1) ->
                          let uu____3178 = explode r2  in
                          (match uu____3178 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3199 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3202 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3199
                                   uu____3202
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____3266  ->
                       fun r  ->
                         match uu____3266 with
                         | (a,q) ->
                             let r' = traverse f pol e a  in
                             comb2
                               (fun a1  -> fun args1  -> (a1, q) :: args1) r'
                               r) args (tpure [])
                   in
                comb2
                  (fun hd2  ->
                     fun args1  -> FStar_Syntax_Syntax.Tm_app (hd2, args1))
                  r0 r1
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____3418 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____3418 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____3458  ->
                            match uu____3458 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____3480 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___357_3512 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___357_3512.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___357_3512.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____3480 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____3540 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____3540.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____3586 = traverse f pol e t1  in
                let uu____3591 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____3591 uu____3586
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___358_3631 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___358_3631.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___358_3631.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____3638 =
                f pol e
                  (let uu___359_3642 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___359_3642.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___359_3642.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____3638
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___360_3652 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___360_3652.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___360_3652.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____3653 = explode rp  in
              (match uu____3653 with
               | (uu____3662,p',gs') ->
                   Dual
                     ((let uu___361_3672 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___361_3672.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___361_3672.FStar_Syntax_Syntax.vars)
                       }), p', (FStar_List.append gs gs')))
  
let (getprop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant] e t
         in
      FStar_Syntax_Util.un_squash tn
  
let (preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term,FStar_Options.optionstate)
        FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun env  ->
    fun goal  ->
      (let uu____3715 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____3715);
      (let uu____3736 = FStar_ST.op_Bang tacdbg  in
       if uu____3736
       then
         let uu____3756 =
           let uu____3757 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____3757
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____3758 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3756
           uu____3758
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____3787 =
         let uu____3796 = traverse by_tactic_interp Pos env goal  in
         match uu____3796 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____3820 -> failwith "no"  in
       match uu____3787 with
       | (t',gs) ->
           ((let uu____3848 = FStar_ST.op_Bang tacdbg  in
             if uu____3848
             then
               let uu____3868 =
                 let uu____3869 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____3869
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____3870 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____3868 uu____3870
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3918  ->
                    fun g  ->
                      match uu____3918 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3963 =
                              let uu____3966 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____3967 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____3966 uu____3967  in
                            match uu____3963 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3968 =
                                  let uu____3973 =
                                    let uu____3974 =
                                      let uu____3975 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____3975
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____3974
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____3973)
                                   in
                                FStar_Errors.raise_error uu____3968
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____3978 = FStar_ST.op_Bang tacdbg  in
                            if uu____3978
                            then
                              let uu____3998 = FStar_Util.string_of_int n1
                                 in
                              let uu____3999 =
                                let uu____4000 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____4000
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____3998 uu____3999
                            else ());
                           (let gt' =
                              let uu____4003 =
                                let uu____4004 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4004
                                 in
                              FStar_TypeChecker_Util.label uu____4003
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____4005 =
                              let uu____4014 =
                                let uu____4021 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____4021, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____4014 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____4005)))) s
                 gs
                in
             let uu____4036 = s1  in
             match uu____4036 with
             | (uu____4057,gs1) ->
                 let uu____4075 =
                   let uu____4082 = FStar_Options.peek ()  in
                   (env, t', uu____4082)  in
                 uu____4075 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4095 =
        let uu____4096 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4096  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4095 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4097 =
      let uu____4102 =
        let uu____4103 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4112 =
          let uu____4123 = FStar_Syntax_Syntax.as_arg a  in [uu____4123]  in
        uu____4103 :: uu____4112  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4102  in
    uu____4097 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        if env.FStar_TypeChecker_Env.nosynth
        then
          let uu____4173 =
            let uu____4178 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____4179 =
              let uu____4180 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4180]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____4178 uu____4179  in
          uu____4173 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____4209 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____4209);
           (let uu____4229 =
              let uu____4236 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____4236 env typ
               in
            match uu____4229 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____4251 =
                        let uu____4254 = FStar_Tactics_Types.goal_env g  in
                        let uu____4255 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____4254 uu____4255  in
                      match uu____4251 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____4258 = FStar_ST.op_Bang tacdbg  in
                            if uu____4258
                            then
                              let uu____4278 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____4278
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____4289 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____4289 guard))
                      | FStar_Pervasives_Native.None  ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                              "synthesis left open goals")
                            typ.FStar_Syntax_Syntax.pos) gs;
                 w)))
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      if env.FStar_TypeChecker_Env.nosynth
      then []
      else
        ((let uu____4306 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____4306);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____4327 =
            let uu____4334 = reify_tactic tau  in
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos uu____4334 env typ
             in
          match uu____4327 with
          | (gs,w) ->
              ((let uu____4344 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____4348 =
                         let uu____4349 =
                           let uu____4352 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____4353 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____4352 uu____4353  in
                         FStar_Option.isSome uu____4349  in
                       Prims.op_Negation uu____4348) gs
                   in
                if uu____4344
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                      "splice left open goals") typ.FStar_Syntax_Syntax.pos
                else ());
               (let w1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Weak;
                    FStar_TypeChecker_Env.HNF;
                    FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant;
                    FStar_TypeChecker_Env.Primops;
                    FStar_TypeChecker_Env.Unascribe;
                    FStar_TypeChecker_Env.Unmeta] env w
                   in
                (let uu____4357 = FStar_ST.op_Bang tacdbg  in
                 if uu____4357
                 then
                   let uu____4377 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____4377
                 else ());
                (let uu____4379 =
                   let uu____4384 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____4384 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____4379 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  