open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec e_tactic_0 :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____235 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____242  ->
         fun uu____243  ->
           fun uu____244  ->
             fun uu____245  -> failwith "Impossible: embedding tactic (0)?")
      (fun t  ->
         fun w  ->
           fun norm1  ->
             let uu____278 = unembed_tactic_0 er t norm1  in
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____278)
      uu____235

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____297 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____307  ->
           fun uu____308  ->
             fun uu____309  ->
               fun uu____310  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  -> fun w  -> unembed_tactic_1 ea er t) uu____297

and e_tactic_nbe_0 :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    FStar_TypeChecker_NBETerm.mk_emb
      (fun uu____346  -> failwith "Impossible: NBE embedding tactic (0)?")
      (fun t  ->
         let uu____352 = unembed_tactic_nbe_0 er t  in
         FStar_All.pipe_left
           (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____352)
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
        (fun uu____375  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun t  -> unembed_tactic_nbe_1 ea er t)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____382  ->
    let tracepoint1 =
      let uu___349_386 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____387 = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____387;
        FStar_TypeChecker_Cfg.arity =
          (uu___349_386.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___349_386.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___349_386.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___349_386.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___349_386.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___349_386.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___349_386.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let set_proofstate_range1 =
      let uu___350_389 =
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
      let uu____390 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Cfg.name = uu____390;
        FStar_TypeChecker_Cfg.arity =
          (uu___350_389.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___350_389.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___350_389.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___350_389.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___350_389.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___350_389.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___350_389.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let incr_depth1 =
      let uu___351_392 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "incr_depth"
          FStar_Tactics_Types.incr_depth FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.incr_depth
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____393 = FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____393;
        FStar_TypeChecker_Cfg.arity =
          (uu___351_392.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___351_392.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___351_392.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___351_392.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___351_392.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___351_392.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___351_392.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let decr_depth1 =
      let uu___352_395 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "decr_depth"
          FStar_Tactics_Types.decr_depth FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.decr_depth
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____396 = FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____396;
        FStar_TypeChecker_Cfg.arity =
          (uu___352_395.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___352_395.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___352_395.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___352_395.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___352_395.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___352_395.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___352_395.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let uu____397 =
      let uu____400 =
        let uu____403 =
          let uu____406 =
            let uu____409 =
              let uu____412 =
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
              let uu____469 =
                let uu____472 =
                  FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                    "fail" (fun uu____474  -> FStar_Tactics_Basic.fail)
                    FStar_Syntax_Embeddings.e_any
                    FStar_Syntax_Embeddings.e_string
                    FStar_Syntax_Embeddings.e_any
                    (fun uu____476  -> FStar_Tactics_Basic.fail)
                    FStar_TypeChecker_NBETerm.e_any
                    FStar_TypeChecker_NBETerm.e_string
                    FStar_TypeChecker_NBETerm.e_any
                   in
                let uu____477 =
                  let uu____480 =
                    FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                      "trivial" FStar_Tactics_Basic.trivial
                      FStar_Syntax_Embeddings.e_unit
                      FStar_Syntax_Embeddings.e_unit
                      FStar_Tactics_Basic.trivial
                      FStar_TypeChecker_NBETerm.e_unit
                      FStar_TypeChecker_NBETerm.e_unit
                     in
                  let uu____481 =
                    let uu____484 =
                      let uu____485 =
                        e_tactic_0 FStar_Syntax_Embeddings.e_any  in
                      let uu____490 =
                        FStar_Syntax_Embeddings.e_option
                          FStar_Syntax_Embeddings.e_any
                         in
                      let uu____495 =
                        e_tactic_nbe_0 FStar_TypeChecker_NBETerm.e_any  in
                      let uu____500 =
                        FStar_TypeChecker_NBETerm.e_option
                          FStar_TypeChecker_NBETerm.e_any
                         in
                      FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                        "__trytac"
                        (fun uu____514  -> FStar_Tactics_Basic.trytac)
                        FStar_Syntax_Embeddings.e_any uu____485 uu____490
                        (fun uu____516  -> FStar_Tactics_Basic.trytac)
                        FStar_TypeChecker_NBETerm.e_any uu____495 uu____500
                       in
                    let uu____517 =
                      let uu____520 =
                        FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                          "intro" FStar_Tactics_Basic.intro
                          FStar_Syntax_Embeddings.e_unit
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Tactics_Basic.intro
                          FStar_TypeChecker_NBETerm.e_unit
                          FStar_Reflection_NBEEmbeddings.e_binder
                         in
                      let uu____521 =
                        let uu____524 =
                          let uu____525 =
                            FStar_Syntax_Embeddings.e_tuple2
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder
                             in
                          let uu____532 =
                            FStar_TypeChecker_NBETerm.e_tuple2
                              FStar_Reflection_NBEEmbeddings.e_binder
                              FStar_Reflection_NBEEmbeddings.e_binder
                             in
                          FStar_Tactics_InterpFuns.mktac1
                            (Prims.parse_int "0") "intro_rec"
                            FStar_Tactics_Basic.intro_rec
                            FStar_Syntax_Embeddings.e_unit uu____525
                            FStar_Tactics_Basic.intro_rec
                            FStar_TypeChecker_NBETerm.e_unit uu____532
                           in
                        let uu____547 =
                          let uu____550 =
                            let uu____551 =
                              FStar_Syntax_Embeddings.e_list
                                FStar_Syntax_Embeddings.e_norm_step
                               in
                            let uu____556 =
                              FStar_TypeChecker_NBETerm.e_list
                                FStar_TypeChecker_NBETerm.e_norm_step
                               in
                            FStar_Tactics_InterpFuns.mktac1
                              (Prims.parse_int "0") "norm"
                              FStar_Tactics_Basic.norm uu____551
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Tactics_Basic.norm uu____556
                              FStar_TypeChecker_NBETerm.e_unit
                             in
                          let uu____565 =
                            let uu____568 =
                              let uu____569 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_norm_step
                                 in
                              let uu____574 =
                                FStar_TypeChecker_NBETerm.e_list
                                  FStar_TypeChecker_NBETerm.e_norm_step
                                 in
                              FStar_Tactics_InterpFuns.mktac3
                                (Prims.parse_int "0") "norm_term_env"
                                FStar_Tactics_Basic.norm_term_env
                                FStar_Reflection_Embeddings.e_env uu____569
                                FStar_Reflection_Embeddings.e_term
                                FStar_Reflection_Embeddings.e_term
                                FStar_Tactics_Basic.norm_term_env
                                FStar_Reflection_NBEEmbeddings.e_env
                                uu____574
                                FStar_Reflection_NBEEmbeddings.e_term
                                FStar_Reflection_NBEEmbeddings.e_term
                               in
                            let uu____583 =
                              let uu____586 =
                                let uu____587 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Syntax_Embeddings.e_norm_step
                                   in
                                let uu____592 =
                                  FStar_TypeChecker_NBETerm.e_list
                                    FStar_TypeChecker_NBETerm.e_norm_step
                                   in
                                FStar_Tactics_InterpFuns.mktac2
                                  (Prims.parse_int "0") "norm_binder_type"
                                  FStar_Tactics_Basic.norm_binder_type
                                  uu____587
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Tactics_Basic.norm_binder_type
                                  uu____592
                                  FStar_Reflection_NBEEmbeddings.e_binder
                                  FStar_TypeChecker_NBETerm.e_unit
                                 in
                              let uu____601 =
                                let uu____604 =
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
                                let uu____605 =
                                  let uu____608 =
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "binder_retype"
                                      FStar_Tactics_Basic.binder_retype
                                      FStar_Reflection_Embeddings.e_binder
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.binder_retype
                                      FStar_Reflection_NBEEmbeddings.e_binder
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____609 =
                                    let uu____612 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        (Prims.parse_int "0") "revert"
                                        FStar_Tactics_Basic.revert
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.revert
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____613 =
                                      let uu____616 =
                                        FStar_Tactics_InterpFuns.mktac1
                                          (Prims.parse_int "0") "clear_top"
                                          FStar_Tactics_Basic.clear_top
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Tactics_Basic.clear_top
                                          FStar_TypeChecker_NBETerm.e_unit
                                          FStar_TypeChecker_NBETerm.e_unit
                                         in
                                      let uu____617 =
                                        let uu____620 =
                                          FStar_Tactics_InterpFuns.mktac1
                                            (Prims.parse_int "0") "clear"
                                            FStar_Tactics_Basic.clear
                                            FStar_Reflection_Embeddings.e_binder
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_Tactics_Basic.clear
                                            FStar_Reflection_NBEEmbeddings.e_binder
                                            FStar_TypeChecker_NBETerm.e_unit
                                           in
                                        let uu____621 =
                                          let uu____624 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              (Prims.parse_int "0") "rewrite"
                                              FStar_Tactics_Basic.rewrite
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Tactics_Basic.rewrite
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                              FStar_TypeChecker_NBETerm.e_unit
                                             in
                                          let uu____625 =
                                            let uu____628 =
                                              FStar_Tactics_InterpFuns.mktac1
                                                (Prims.parse_int "0") "smt"
                                                FStar_Tactics_Basic.smt
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Tactics_Basic.smt
                                                FStar_TypeChecker_NBETerm.e_unit
                                                FStar_TypeChecker_NBETerm.e_unit
                                               in
                                            let uu____629 =
                                              let uu____632 =
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
                                              let uu____633 =
                                                let uu____636 =
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
                                                let uu____637 =
                                                  let uu____640 =
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
                                                  let uu____641 =
                                                    let uu____644 =
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
                                                    let uu____645 =
                                                      let uu____648 =
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
                                                      let uu____649 =
                                                        let uu____652 =
                                                          let uu____653 =
                                                            e_tactic_0
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____658 =
                                                            e_tactic_0
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____663 =
                                                            FStar_Syntax_Embeddings.e_tuple2
                                                              FStar_Syntax_Embeddings.e_any
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____670 =
                                                            e_tactic_nbe_0
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          let uu____675 =
                                                            e_tactic_nbe_0
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          let uu____680 =
                                                            FStar_TypeChecker_NBETerm.e_tuple2
                                                              FStar_TypeChecker_NBETerm.e_any
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          FStar_Tactics_InterpFuns.mktac5
                                                            (Prims.parse_int "2")
                                                            "__divide"
                                                            (fun uu____705 
                                                               ->
                                                               fun uu____706 
                                                                 ->
                                                                 FStar_Tactics_Basic.divide)
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Syntax_Embeddings.e_int
                                                            uu____653
                                                            uu____658
                                                            uu____663
                                                            (fun uu____709 
                                                               ->
                                                               fun uu____710 
                                                                 ->
                                                                 FStar_Tactics_Basic.divide)
                                                            FStar_TypeChecker_NBETerm.e_any
                                                            FStar_TypeChecker_NBETerm.e_any
                                                            FStar_TypeChecker_NBETerm.e_int
                                                            uu____670
                                                            uu____675
                                                            uu____680
                                                           in
                                                        let uu____711 =
                                                          let uu____714 =
                                                            let uu____715 =
                                                              e_tactic_0
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____720 =
                                                              e_tactic_0
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____725 =
                                                              e_tactic_nbe_0
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            let uu____730 =
                                                              e_tactic_nbe_0
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            FStar_Tactics_InterpFuns.mktac2
                                                              (Prims.parse_int "0")
                                                              "__seq"
                                                              FStar_Tactics_Basic.seq
                                                              uu____715
                                                              uu____720
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.seq
                                                              uu____725
                                                              uu____730
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                             in
                                                          let uu____743 =
                                                            let uu____746 =
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
                                                            let uu____747 =
                                                              let uu____750 =
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
                                                              let uu____751 =
                                                                let uu____754
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
                                                                let uu____755
                                                                  =
                                                                  let uu____758
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____761
                                                                     ->
                                                                    fun
                                                                    uu____762
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                  let uu____765
                                                                    =
                                                                    let uu____768
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
                                                                    let uu____769
                                                                    =
                                                                    let uu____772
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
                                                                    let uu____773
                                                                    =
                                                                    let uu____776
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
                                                                    let uu____777
                                                                    =
                                                                    let uu____780
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
                                                                    let uu____781
                                                                    =
                                                                    let uu____784
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
                                                                    let uu____785
                                                                    =
                                                                    let uu____788
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
                                                                    let uu____789
                                                                    =
                                                                    let uu____792
                                                                    =
                                                                    let uu____793
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____798
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____793
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____798
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____807
                                                                    =
                                                                    let uu____810
                                                                    =
                                                                    let uu____811
                                                                    =
                                                                    let uu____823
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____823
                                                                     in
                                                                    let uu____834
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____839
                                                                    =
                                                                    let uu____851
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____851
                                                                     in
                                                                    let uu____862
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____811
                                                                    uu____834
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____839
                                                                    uu____862
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____889
                                                                    =
                                                                    let uu____892
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
                                                                    let uu____893
                                                                    =
                                                                    let uu____896
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
                                                                    let uu____897
                                                                    =
                                                                    let uu____900
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
                                                                    let uu____901
                                                                    =
                                                                    let uu____904
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
                                                                    let uu____905
                                                                    =
                                                                    let uu____908
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
                                                                    let uu____909
                                                                    =
                                                                    let uu____912
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
                                                                    let uu____913
                                                                    =
                                                                    let uu____916
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
                                                                    let uu____917
                                                                    =
                                                                    let uu____920
                                                                    =
                                                                    let uu____921
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____928
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
                                                                    uu____921
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____928
                                                                     in
                                                                    let uu____943
                                                                    =
                                                                    let uu____946
                                                                    =
                                                                    let uu____947
                                                                    =
                                                                    let uu____956
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____956
                                                                     in
                                                                    let uu____967
                                                                    =
                                                                    let uu____976
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____976
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____947
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____967
                                                                     in
                                                                    let uu____999
                                                                    =
                                                                    let uu____1002
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
                                                                    let uu____1003
                                                                    =
                                                                    let uu____1006
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
                                                                    let uu____1007
                                                                    =
                                                                    let uu____1010
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
                                                                    let uu____1011
                                                                    =
                                                                    let uu____1014
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
                                                                    let uu____1015
                                                                    =
                                                                    let uu____1018
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
                                                                    let uu____1019
                                                                    =
                                                                    let uu____1022
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
                                                                    let uu____1023
                                                                    =
                                                                    let uu____1026
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
                                                                    let uu____1027
                                                                    =
                                                                    let uu____1030
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
                                                                    let uu____1031
                                                                    =
                                                                    let uu____1034
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
                                                                    let uu____1035
                                                                    =
                                                                    let uu____1038
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
                                                                    let uu____1039
                                                                    =
                                                                    let uu____1042
                                                                    =
                                                                    let uu____1043
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1048
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1043
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1048
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1057
                                                                    =
                                                                    let uu____1060
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
                                                                    let uu____1061
                                                                    =
                                                                    let uu____1064
                                                                    =
                                                                    let uu____1065
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1070
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1065
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1070
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1079
                                                                    =
                                                                    let uu____1082
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
                                                                    let uu____1083
                                                                    =
                                                                    let uu____1086
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
                                                                    let uu____1087
                                                                    =
                                                                    let uu____1090
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
                                                                    let uu____1091
                                                                    =
                                                                    let uu____1094
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
                                                                    let uu____1095
                                                                    =
                                                                    let uu____1098
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
                                                                    [uu____1098]
                                                                     in
                                                                    uu____1094
                                                                    ::
                                                                    uu____1095
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
                                                                    uu____1064
                                                                    ::
                                                                    uu____1079
                                                                     in
                                                                    uu____1060
                                                                    ::
                                                                    uu____1061
                                                                     in
                                                                    uu____1042
                                                                    ::
                                                                    uu____1057
                                                                     in
                                                                    uu____1038
                                                                    ::
                                                                    uu____1039
                                                                     in
                                                                    uu____1034
                                                                    ::
                                                                    uu____1035
                                                                     in
                                                                    uu____1030
                                                                    ::
                                                                    uu____1031
                                                                     in
                                                                    uu____1026
                                                                    ::
                                                                    uu____1027
                                                                     in
                                                                    uu____1022
                                                                    ::
                                                                    uu____1023
                                                                     in
                                                                    uu____1018
                                                                    ::
                                                                    uu____1019
                                                                     in
                                                                    uu____1014
                                                                    ::
                                                                    uu____1015
                                                                     in
                                                                    uu____1010
                                                                    ::
                                                                    uu____1011
                                                                     in
                                                                    uu____1006
                                                                    ::
                                                                    uu____1007
                                                                     in
                                                                    uu____1002
                                                                    ::
                                                                    uu____1003
                                                                     in
                                                                    uu____946
                                                                    ::
                                                                    uu____999
                                                                     in
                                                                    uu____920
                                                                    ::
                                                                    uu____943
                                                                     in
                                                                    uu____916
                                                                    ::
                                                                    uu____917
                                                                     in
                                                                    uu____912
                                                                    ::
                                                                    uu____913
                                                                     in
                                                                    uu____908
                                                                    ::
                                                                    uu____909
                                                                     in
                                                                    uu____904
                                                                    ::
                                                                    uu____905
                                                                     in
                                                                    uu____900
                                                                    ::
                                                                    uu____901
                                                                     in
                                                                    uu____896
                                                                    ::
                                                                    uu____897
                                                                     in
                                                                    uu____892
                                                                    ::
                                                                    uu____893
                                                                     in
                                                                    uu____810
                                                                    ::
                                                                    uu____889
                                                                     in
                                                                    uu____792
                                                                    ::
                                                                    uu____807
                                                                     in
                                                                    uu____788
                                                                    ::
                                                                    uu____789
                                                                     in
                                                                    uu____784
                                                                    ::
                                                                    uu____785
                                                                     in
                                                                    uu____780
                                                                    ::
                                                                    uu____781
                                                                     in
                                                                    uu____776
                                                                    ::
                                                                    uu____777
                                                                     in
                                                                    uu____772
                                                                    ::
                                                                    uu____773
                                                                     in
                                                                    uu____768
                                                                    ::
                                                                    uu____769
                                                                     in
                                                                  uu____758
                                                                    ::
                                                                    uu____765
                                                                   in
                                                                uu____754 ::
                                                                  uu____755
                                                                 in
                                                              uu____750 ::
                                                                uu____751
                                                               in
                                                            uu____746 ::
                                                              uu____747
                                                             in
                                                          uu____714 ::
                                                            uu____743
                                                           in
                                                        uu____652 ::
                                                          uu____711
                                                         in
                                                      uu____648 :: uu____649
                                                       in
                                                    uu____644 :: uu____645
                                                     in
                                                  uu____640 :: uu____641  in
                                                uu____636 :: uu____637  in
                                              uu____632 :: uu____633  in
                                            uu____628 :: uu____629  in
                                          uu____624 :: uu____625  in
                                        uu____620 :: uu____621  in
                                      uu____616 :: uu____617  in
                                    uu____612 :: uu____613  in
                                  uu____608 :: uu____609  in
                                uu____604 :: uu____605  in
                              uu____586 :: uu____601  in
                            uu____568 :: uu____583  in
                          uu____550 :: uu____565  in
                        uu____524 :: uu____547  in
                      uu____520 :: uu____521  in
                    uu____484 :: uu____517  in
                  uu____480 :: uu____481  in
                uu____472 :: uu____477  in
              uu____412 :: uu____469  in
            set_proofstate_range1 :: uu____409  in
          tracepoint1 :: uu____406  in
        decr_depth1 :: uu____403  in
      incr_depth1 :: uu____400  in
    FStar_List.append uu____397
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
                 let uu____1126 =
                   let uu____1131 =
                     let uu____1132 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____1132]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1131  in
                 uu____1126 FStar_Pervasives_Native.None rng  in
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
               let uu____1185 =
                 let uu____1190 =
                   let uu____1191 =
                     let uu____1200 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1200  in
                   [uu____1191]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1190  in
               uu____1185 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1245 = FStar_Options.tactics_nbe ()  in
               if uu____1245
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____1264 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____1264)
             else ();
             (let result =
                let uu____1267 = primitive_steps ()  in
                norm_f uu____1267 steps
                  proof_state.FStar_Tactics_Types.main_context tm
                 in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____1271 = FStar_Syntax_Print.term_to_string result
                    in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____1271)
              else ();
              (let res =
                 let uu____1278 = FStar_Tactics_Embedding.e_result eb  in
                 FStar_Tactics_InterpFuns.unembed uu____1278 result ncb  in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b,ps)) ->
                   let uu____1293 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1293
                     (fun uu____1297  -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (msg,ps)) ->
                   let uu____1302 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1302
                     (fun uu____1306  -> FStar_Tactics_Basic.fail msg)
               | FStar_Pervasives_Native.None  ->
                   let uu____1309 =
                     let uu____1314 =
                       let uu____1315 =
                         FStar_Syntax_Print.term_to_string result  in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____1315
                        in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____1314)  in
                   FStar_Errors.raise_error uu____1309
                     (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.t ->
          ('Aa -> 'Ar FStar_Tactics_Basic.tac) FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        FStar_Pervasives_Native.Some
          (fun x  ->
             let x_tm = FStar_TypeChecker_NBETerm.embed ea x  in
             let app =
               let uu____1336 =
                 let uu____1337 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                 [uu____1337]  in
               FStar_TypeChecker_NBE.iapp f uu____1336  in
             unembed_tactic_nbe_0 er app)

and unembed_tactic_nbe_0 :
  'Ab .
    'Ab FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.t -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun embedded_tac_b  ->
      FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
        (fun proof_state  ->
           let result =
             let uu____1362 =
               let uu____1363 =
                 let uu____1368 =
                   FStar_TypeChecker_NBETerm.embed
                     FStar_Tactics_Embedding.e_proofstate_nbe proof_state
                    in
                 FStar_TypeChecker_NBETerm.as_arg uu____1368  in
               [uu____1363]  in
             FStar_TypeChecker_NBE.iapp embedded_tac_b uu____1362  in
           let res =
             let uu____1382 = FStar_Tactics_Embedding.e_result_nbe eb  in
             FStar_TypeChecker_NBETerm.unembed uu____1382 result  in
           match res with
           | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
               (b,ps)) ->
               let uu____1395 = FStar_Tactics_Basic.set ps  in
               FStar_Tactics_Basic.bind uu____1395
                 (fun uu____1399  -> FStar_Tactics_Basic.ret b)
           | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
               (msg,ps)) ->
               let uu____1404 = FStar_Tactics_Basic.set ps  in
               FStar_Tactics_Basic.bind uu____1404
                 (fun uu____1408  -> FStar_Tactics_Basic.fail msg)
           | FStar_Pervasives_Native.None  ->
               let uu____1411 =
                 let uu____1416 =
                   let uu____1417 =
                     FStar_TypeChecker_NBETerm.t_to_string result  in
                   FStar_Util.format1
                     "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                     uu____1417
                    in
                 (FStar_Errors.Fatal_TacticGotStuck, uu____1416)  in
               FStar_Errors.raise_error uu____1411
                 (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

let report_implicits :
  'Auu____1426 . 'Auu____1426 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____1455 =
               let uu____1456 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____1457 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____1456 uu____1457 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____1455, (imp.FStar_TypeChecker_Env.imp_range))) is
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
            (let uu____1496 = FStar_ST.op_Bang tacdbg  in
             if uu____1496
             then
               let uu____1516 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____1516
             else ());
            (let uu____1518 =
               FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic  in
             match uu____1518 with
             | (uu____1531,uu____1532,g) ->
                 ((let uu____1535 = FStar_ST.op_Bang tacdbg  in
                   if uu____1535 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb
                      in
                   let uu____1561 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____1561 with
                   | (env1,uu____1575) ->
                       let env2 =
                         let uu___353_1581 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___353_1581.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___353_1581.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___353_1581.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___353_1581.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___353_1581.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___353_1581.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___353_1581.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___353_1581.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___353_1581.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___353_1581.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___353_1581.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___353_1581.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___353_1581.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___353_1581.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___353_1581.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___353_1581.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___353_1581.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___353_1581.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___353_1581.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___353_1581.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___353_1581.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___353_1581.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___353_1581.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___353_1581.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___353_1581.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___353_1581.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___353_1581.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___353_1581.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___353_1581.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___353_1581.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___353_1581.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___353_1581.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___353_1581.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___353_1581.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___353_1581.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___353_1581.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___353_1581.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___353_1581.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___353_1581.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___353_1581.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___353_1581.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___354_1583 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___354_1583.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___354_1583.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___354_1583.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___354_1583.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___354_1583.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___354_1583.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___354_1583.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___354_1583.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___354_1583.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___354_1583.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___354_1583.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___354_1583.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___354_1583.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___354_1583.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___354_1583.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___354_1583.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___354_1583.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___354_1583.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___354_1583.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___354_1583.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___354_1583.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___354_1583.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___354_1583.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___354_1583.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___354_1583.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___354_1583.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___354_1583.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___354_1583.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___354_1583.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___354_1583.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___354_1583.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___354_1583.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___354_1583.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___354_1583.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___354_1583.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___354_1583.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___354_1583.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___354_1583.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___354_1583.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___354_1583.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___354_1583.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___355_1585 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___355_1585.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___355_1585.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___355_1585.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___355_1585.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___355_1585.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___355_1585.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___355_1585.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___355_1585.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___355_1585.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___355_1585.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___355_1585.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___355_1585.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___355_1585.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___355_1585.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___355_1585.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___355_1585.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___355_1585.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___355_1585.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___355_1585.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___355_1585.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___355_1585.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___355_1585.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___355_1585.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___355_1585.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___355_1585.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___355_1585.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___355_1585.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___355_1585.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___355_1585.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___355_1585.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___355_1585.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___355_1585.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___355_1585.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___355_1585.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___355_1585.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___355_1585.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___355_1585.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___355_1585.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___355_1585.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___355_1585.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___355_1585.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____1587 = FStar_Range.use_range rng_goal  in
                         let uu____1588 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____1587 uu____1588  in
                       let uu____1589 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____1589 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____1627 = FStar_ST.op_Bang tacdbg  in
                              if uu____1627
                              then
                                let uu____1647 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____1647
                              else ());
                             (let uu____1649 =
                                FStar_Util.record_time
                                  (fun uu____1659  ->
                                     FStar_Tactics_Basic.run_safe tau ps)
                                 in
                              match uu____1649 with
                              | (res,ms) ->
                                  ((let uu____1673 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____1673
                                    then
                                      let uu____1693 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____1694 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____1695 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "}\nTactic %s ran in %s ms (%s)\n"
                                        uu____1693 uu____1694 uu____1695
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____1703,ps1) ->
                                        ((let uu____1706 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1706
                                          then
                                            let uu____1726 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____1726
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____1733 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____1733
                                              then
                                                let uu____1734 =
                                                  let uu____1735 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____1736 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt
                                                    uu____1735 uu____1736
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____1734
                                                 then ()
                                                 else
                                                   (let uu____1738 =
                                                      let uu____1739 =
                                                        let uu____1740 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____1740
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____1739
                                                       in
                                                    failwith uu____1738))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____1743 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1743
                                          then
                                            let uu____1763 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____1763
                                          else ());
                                         (let g1 =
                                            let uu___356_1768 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___356_1768.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___356_1768.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___356_1768.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____1771 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____1771
                                           then
                                             let uu____1791 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits)
                                                in
                                             let uu____1792 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____1791 uu____1792
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____1798 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____1798
                                            then
                                              let uu____1818 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits)
                                                 in
                                              let uu____1819 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____1818 uu____1819
                                            else ());
                                           report_implicits ps1
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____1825 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____1825
                                            then
                                              let uu____1845 =
                                                let uu____1846 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc
                                                   in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____1846 ps1
                                                 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____1845
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____1853 =
                                            let uu____1854 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____1854 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____1853
                                            "at the time of failure");
                                         (let uu____1855 =
                                            let uu____1860 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____1860)
                                             in
                                          FStar_Errors.raise_error uu____1855
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____1872 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____1878 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____1884 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____1939 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____1979 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2033 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____2074 . 'Auu____2074 -> 'Auu____2074 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____2102 = FStar_Syntax_Util.head_and_args t  in
        match uu____2102 with
        | (hd1,args) ->
            let uu____2145 =
              let uu____2160 =
                let uu____2161 = FStar_Syntax_Util.un_uinst hd1  in
                uu____2161.FStar_Syntax_Syntax.n  in
              (uu____2160, args)  in
            (match uu____2145 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2176))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2239 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2239 with
                       | (gs,uu____2247) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____2254 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2254 with
                       | (gs,uu____2262) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2305 =
                        let uu____2312 =
                          let uu____2315 =
                            let uu____2316 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2316
                             in
                          [uu____2315]  in
                        (FStar_Syntax_Util.t_true, uu____2312)  in
                      Simplified uu____2305
                  | Both  ->
                      let uu____2327 =
                        let uu____2336 =
                          let uu____2339 =
                            let uu____2340 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2340
                             in
                          [uu____2339]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____2336)  in
                      Dual uu____2327
                  | Neg  -> Simplified (assertion, []))
             | uu____2353 -> Unchanged t)
  
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
    fun uu___348_2443  ->
      match uu___348_2443 with
      | Unchanged t -> let uu____2449 = f t  in Unchanged uu____2449
      | Simplified (t,gs) ->
          let uu____2456 = let uu____2463 = f t  in (uu____2463, gs)  in
          Simplified uu____2456
      | Dual (tn,tp,gs) ->
          let uu____2473 =
            let uu____2482 = f tn  in
            let uu____2483 = f tp  in (uu____2482, uu____2483, gs)  in
          Dual uu____2473
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____2546 = f t1 t2  in Unchanged uu____2546
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____2558 = let uu____2565 = f t1 t2  in (uu____2565, gs)
               in
            Simplified uu____2558
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____2579 = let uu____2586 = f t1 t2  in (uu____2586, gs)
               in
            Simplified uu____2579
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____2605 =
              let uu____2612 = f t1 t2  in
              (uu____2612, (FStar_List.append gs1 gs2))  in
            Simplified uu____2605
        | uu____2615 ->
            let uu____2624 = explode x  in
            (match uu____2624 with
             | (n1,p1,gs1) ->
                 let uu____2642 = explode y  in
                 (match uu____2642 with
                  | (n2,p2,gs2) ->
                      let uu____2660 =
                        let uu____2669 = f n1 n2  in
                        let uu____2670 = f p1 p2  in
                        (uu____2669, uu____2670, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____2660))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____2742 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____2742
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____2790  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____2832 =
              let uu____2833 = FStar_Syntax_Subst.compress t  in
              uu____2833.FStar_Syntax_Syntax.n  in
            match uu____2832 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____2845 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____2845 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____2871 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____2871 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2891;
                   FStar_Syntax_Syntax.vars = uu____2892;_},(p,uu____2894)::
                 (q,uu____2896)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____2952 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2952
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____2955 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____2955 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____2969 = FStar_Syntax_Util.mk_imp l r  in
                       uu____2969.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2973;
                   FStar_Syntax_Syntax.vars = uu____2974;_},(p,uu____2976)::
                 (q,uu____2978)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3034 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3034
                   in
                let xq =
                  let uu____3036 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3036
                   in
                let r1 =
                  let uu____3038 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3038 p  in
                let r2 =
                  let uu____3040 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3040 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3047,Unchanged uu____3048) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3066 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3066.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3069 ->
                     let uu____3078 = explode r1  in
                     (match uu____3078 with
                      | (pn,pp,gs1) ->
                          let uu____3096 = explode r2  in
                          (match uu____3096 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3117 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3120 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3117
                                   uu____3120
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____3184  ->
                       fun r  ->
                         match uu____3184 with
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
                let uu____3336 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____3336 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____3376  ->
                            match uu____3376 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____3398 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___357_3430 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___357_3430.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___357_3430.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____3398 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____3458 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____3458.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____3504 = traverse f pol e t1  in
                let uu____3509 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____3509 uu____3504
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___358_3549 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___358_3549.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___358_3549.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____3556 =
                f pol e
                  (let uu___359_3560 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___359_3560.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___359_3560.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____3556
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___360_3570 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___360_3570.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___360_3570.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____3571 = explode rp  in
              (match uu____3571 with
               | (uu____3580,p',gs') ->
                   Dual
                     ((let uu___361_3590 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___361_3590.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___361_3590.FStar_Syntax_Syntax.vars)
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
      (let uu____3633 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____3633);
      (let uu____3654 = FStar_ST.op_Bang tacdbg  in
       if uu____3654
       then
         let uu____3674 =
           let uu____3675 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____3675
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____3676 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3674
           uu____3676
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____3705 =
         let uu____3714 = traverse by_tactic_interp Pos env goal  in
         match uu____3714 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____3738 -> failwith "no"  in
       match uu____3705 with
       | (t',gs) ->
           ((let uu____3766 = FStar_ST.op_Bang tacdbg  in
             if uu____3766
             then
               let uu____3786 =
                 let uu____3787 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____3787
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____3788 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____3786 uu____3788
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3836  ->
                    fun g  ->
                      match uu____3836 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3881 =
                              let uu____3884 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____3885 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____3884 uu____3885  in
                            match uu____3881 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3886 =
                                  let uu____3891 =
                                    let uu____3892 =
                                      let uu____3893 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____3893
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____3892
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____3891)
                                   in
                                FStar_Errors.raise_error uu____3886
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____3896 = FStar_ST.op_Bang tacdbg  in
                            if uu____3896
                            then
                              let uu____3916 = FStar_Util.string_of_int n1
                                 in
                              let uu____3917 =
                                let uu____3918 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____3918
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____3916 uu____3917
                            else ());
                           (let gt' =
                              let uu____3921 =
                                let uu____3922 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____3922
                                 in
                              FStar_TypeChecker_Util.label uu____3921
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____3923 =
                              let uu____3932 =
                                let uu____3939 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____3939, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____3932 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____3923)))) s
                 gs
                in
             let uu____3954 = s1  in
             match uu____3954 with
             | (uu____3975,gs1) ->
                 let uu____3993 =
                   let uu____4000 = FStar_Options.peek ()  in
                   (env, t', uu____4000)  in
                 uu____3993 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4013 =
        let uu____4014 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4014  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4013 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4015 =
      let uu____4020 =
        let uu____4021 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4030 =
          let uu____4041 = FStar_Syntax_Syntax.as_arg a  in [uu____4041]  in
        uu____4021 :: uu____4030  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4020  in
    uu____4015 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
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
          let uu____4091 =
            let uu____4096 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____4097 =
              let uu____4098 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4098]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____4096 uu____4097  in
          uu____4091 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____4127 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____4127);
           (let uu____4147 =
              let uu____4154 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____4154 env typ
               in
            match uu____4147 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____4169 =
                        let uu____4172 = FStar_Tactics_Types.goal_env g  in
                        let uu____4173 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____4172 uu____4173  in
                      match uu____4169 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____4176 = FStar_ST.op_Bang tacdbg  in
                            if uu____4176
                            then
                              let uu____4196 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____4196
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____4207 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____4207 guard))
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
        ((let uu____4224 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____4224);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____4245 =
            let uu____4252 = reify_tactic tau  in
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos uu____4252 env typ
             in
          match uu____4245 with
          | (gs,w) ->
              ((let uu____4262 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____4266 =
                         let uu____4267 =
                           let uu____4270 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____4271 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____4270 uu____4271  in
                         FStar_Option.isSome uu____4267  in
                       Prims.op_Negation uu____4266) gs
                   in
                if uu____4262
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
                (let uu____4275 = FStar_ST.op_Bang tacdbg  in
                 if uu____4275
                 then
                   let uu____4295 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____4295
                 else ());
                (let uu____4297 =
                   let uu____4302 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____4302 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____4297 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  