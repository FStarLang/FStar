open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec e_tactic_0 :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____330 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____337  ->
         fun uu____338  ->
           fun uu____339  ->
             fun uu____340  -> failwith "Impossible: embedding tactic (0)?")
      (fun t  ->
         fun w  ->
           fun norm1  ->
             let uu____373 = unembed_tactic_0 er t norm1  in
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____373)
      uu____330

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____392 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____402  ->
           fun uu____403  ->
             fun uu____404  ->
               fun uu____405  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  -> fun w  -> unembed_tactic_1 ea er t) uu____392

and e_tactic_nbe_0 :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____443  -> failwith "Impossible: NBE embedding tactic (0)?")
      (fun cb  ->
         fun t  ->
           let uu____459 = unembed_tactic_nbe_0 er cb t  in
           FStar_All.pipe_left
             (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____459)
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
           fun uu____488  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  -> fun t  -> unembed_tactic_nbe_1 ea er cb t)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____509  ->
    let tracepoint1 =
      let uu___349_513 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____514 = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____514;
        FStar_TypeChecker_Cfg.arity =
          (uu___349_513.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___349_513.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___349_513.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___349_513.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___349_513.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___349_513.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___349_513.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let set_proofstate_range1 =
      let uu___350_516 =
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
      let uu____517 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Cfg.name = uu____517;
        FStar_TypeChecker_Cfg.arity =
          (uu___350_516.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___350_516.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___350_516.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___350_516.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___350_516.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___350_516.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___350_516.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let incr_depth1 =
      let uu___351_519 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "incr_depth"
          FStar_Tactics_Types.incr_depth FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.incr_depth
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____520 = FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____520;
        FStar_TypeChecker_Cfg.arity =
          (uu___351_519.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___351_519.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___351_519.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___351_519.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___351_519.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___351_519.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___351_519.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let decr_depth1 =
      let uu___352_522 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "decr_depth"
          FStar_Tactics_Types.decr_depth FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.decr_depth
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____523 = FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____523;
        FStar_TypeChecker_Cfg.arity =
          (uu___352_522.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___352_522.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___352_522.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___352_522.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___352_522.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___352_522.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___352_522.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let uu____524 =
      let uu____527 =
        let uu____530 =
          let uu____533 =
            let uu____536 =
              let uu____539 =
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
              let uu____596 =
                let uu____599 =
                  FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                    "fail" (fun uu____601  -> FStar_Tactics_Basic.fail)
                    FStar_Syntax_Embeddings.e_any
                    FStar_Syntax_Embeddings.e_string
                    FStar_Syntax_Embeddings.e_any
                    (fun uu____603  -> FStar_Tactics_Basic.fail)
                    FStar_TypeChecker_NBETerm.e_any
                    FStar_TypeChecker_NBETerm.e_string
                    FStar_TypeChecker_NBETerm.e_any
                   in
                let uu____604 =
                  let uu____607 =
                    FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                      "trivial" FStar_Tactics_Basic.trivial
                      FStar_Syntax_Embeddings.e_unit
                      FStar_Syntax_Embeddings.e_unit
                      FStar_Tactics_Basic.trivial
                      FStar_TypeChecker_NBETerm.e_unit
                      FStar_TypeChecker_NBETerm.e_unit
                     in
                  let uu____608 =
                    let uu____611 =
                      let uu____612 =
                        e_tactic_0 FStar_Syntax_Embeddings.e_any  in
                      let uu____617 =
                        FStar_Syntax_Embeddings.e_either
                          FStar_Syntax_Embeddings.e_string
                          FStar_Syntax_Embeddings.e_any
                         in
                      let uu____624 =
                        e_tactic_nbe_0 FStar_TypeChecker_NBETerm.e_any  in
                      let uu____629 =
                        FStar_TypeChecker_NBETerm.e_either
                          FStar_TypeChecker_NBETerm.e_string
                          FStar_TypeChecker_NBETerm.e_any
                         in
                      FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                        "__catch"
                        (fun uu____649  -> FStar_Tactics_Basic.catch)
                        FStar_Syntax_Embeddings.e_any uu____612 uu____617
                        (fun uu____651  -> FStar_Tactics_Basic.catch)
                        FStar_TypeChecker_NBETerm.e_any uu____624 uu____629
                       in
                    let uu____652 =
                      let uu____655 =
                        FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                          "intro" FStar_Tactics_Basic.intro
                          FStar_Syntax_Embeddings.e_unit
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Tactics_Basic.intro
                          FStar_TypeChecker_NBETerm.e_unit
                          FStar_Reflection_NBEEmbeddings.e_binder
                         in
                      let uu____656 =
                        let uu____659 =
                          let uu____660 =
                            FStar_Syntax_Embeddings.e_tuple2
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder
                             in
                          let uu____667 =
                            FStar_TypeChecker_NBETerm.e_tuple2
                              FStar_Reflection_NBEEmbeddings.e_binder
                              FStar_Reflection_NBEEmbeddings.e_binder
                             in
                          FStar_Tactics_InterpFuns.mktac1
                            (Prims.parse_int "0") "intro_rec"
                            FStar_Tactics_Basic.intro_rec
                            FStar_Syntax_Embeddings.e_unit uu____660
                            FStar_Tactics_Basic.intro_rec
                            FStar_TypeChecker_NBETerm.e_unit uu____667
                           in
                        let uu____682 =
                          let uu____685 =
                            let uu____686 =
                              FStar_Syntax_Embeddings.e_list
                                FStar_Syntax_Embeddings.e_norm_step
                               in
                            let uu____691 =
                              FStar_TypeChecker_NBETerm.e_list
                                FStar_TypeChecker_NBETerm.e_norm_step
                               in
                            FStar_Tactics_InterpFuns.mktac1
                              (Prims.parse_int "0") "norm"
                              FStar_Tactics_Basic.norm uu____686
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Tactics_Basic.norm uu____691
                              FStar_TypeChecker_NBETerm.e_unit
                             in
                          let uu____700 =
                            let uu____703 =
                              let uu____704 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_norm_step
                                 in
                              let uu____709 =
                                FStar_TypeChecker_NBETerm.e_list
                                  FStar_TypeChecker_NBETerm.e_norm_step
                                 in
                              FStar_Tactics_InterpFuns.mktac3
                                (Prims.parse_int "0") "norm_term_env"
                                FStar_Tactics_Basic.norm_term_env
                                FStar_Reflection_Embeddings.e_env uu____704
                                FStar_Reflection_Embeddings.e_term
                                FStar_Reflection_Embeddings.e_term
                                FStar_Tactics_Basic.norm_term_env
                                FStar_Reflection_NBEEmbeddings.e_env
                                uu____709
                                FStar_Reflection_NBEEmbeddings.e_term
                                FStar_Reflection_NBEEmbeddings.e_term
                               in
                            let uu____718 =
                              let uu____721 =
                                let uu____722 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Syntax_Embeddings.e_norm_step
                                   in
                                let uu____727 =
                                  FStar_TypeChecker_NBETerm.e_list
                                    FStar_TypeChecker_NBETerm.e_norm_step
                                   in
                                FStar_Tactics_InterpFuns.mktac2
                                  (Prims.parse_int "0") "norm_binder_type"
                                  FStar_Tactics_Basic.norm_binder_type
                                  uu____722
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Tactics_Basic.norm_binder_type
                                  uu____727
                                  FStar_Reflection_NBEEmbeddings.e_binder
                                  FStar_TypeChecker_NBETerm.e_unit
                                 in
                              let uu____736 =
                                let uu____739 =
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
                                let uu____740 =
                                  let uu____743 =
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "binder_retype"
                                      FStar_Tactics_Basic.binder_retype
                                      FStar_Reflection_Embeddings.e_binder
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.binder_retype
                                      FStar_Reflection_NBEEmbeddings.e_binder
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____744 =
                                    let uu____747 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        (Prims.parse_int "0") "revert"
                                        FStar_Tactics_Basic.revert
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.revert
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____748 =
                                      let uu____751 =
                                        FStar_Tactics_InterpFuns.mktac1
                                          (Prims.parse_int "0") "clear_top"
                                          FStar_Tactics_Basic.clear_top
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Tactics_Basic.clear_top
                                          FStar_TypeChecker_NBETerm.e_unit
                                          FStar_TypeChecker_NBETerm.e_unit
                                         in
                                      let uu____752 =
                                        let uu____755 =
                                          FStar_Tactics_InterpFuns.mktac1
                                            (Prims.parse_int "0") "clear"
                                            FStar_Tactics_Basic.clear
                                            FStar_Reflection_Embeddings.e_binder
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_Tactics_Basic.clear
                                            FStar_Reflection_NBEEmbeddings.e_binder
                                            FStar_TypeChecker_NBETerm.e_unit
                                           in
                                        let uu____756 =
                                          let uu____759 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              (Prims.parse_int "0") "rewrite"
                                              FStar_Tactics_Basic.rewrite
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Tactics_Basic.rewrite
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                              FStar_TypeChecker_NBETerm.e_unit
                                             in
                                          let uu____760 =
                                            let uu____763 =
                                              FStar_Tactics_InterpFuns.mktac1
                                                (Prims.parse_int "0") "smt"
                                                FStar_Tactics_Basic.smt
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Tactics_Basic.smt
                                                FStar_TypeChecker_NBETerm.e_unit
                                                FStar_TypeChecker_NBETerm.e_unit
                                               in
                                            let uu____764 =
                                              let uu____767 =
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
                                              let uu____768 =
                                                let uu____771 =
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
                                                let uu____772 =
                                                  let uu____775 =
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
                                                  let uu____776 =
                                                    let uu____779 =
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
                                                    let uu____780 =
                                                      let uu____783 =
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
                                                      let uu____784 =
                                                        let uu____787 =
                                                          let uu____788 =
                                                            e_tactic_0
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____793 =
                                                            e_tactic_0
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____798 =
                                                            FStar_Syntax_Embeddings.e_tuple2
                                                              FStar_Syntax_Embeddings.e_any
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____805 =
                                                            e_tactic_nbe_0
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          let uu____810 =
                                                            e_tactic_nbe_0
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          let uu____815 =
                                                            FStar_TypeChecker_NBETerm.e_tuple2
                                                              FStar_TypeChecker_NBETerm.e_any
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          FStar_Tactics_InterpFuns.mktac5
                                                            (Prims.parse_int "2")
                                                            "__divide"
                                                            (fun uu____840 
                                                               ->
                                                               fun uu____841 
                                                                 ->
                                                                 FStar_Tactics_Basic.divide)
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Syntax_Embeddings.e_int
                                                            uu____788
                                                            uu____793
                                                            uu____798
                                                            (fun uu____844 
                                                               ->
                                                               fun uu____845 
                                                                 ->
                                                                 FStar_Tactics_Basic.divide)
                                                            FStar_TypeChecker_NBETerm.e_any
                                                            FStar_TypeChecker_NBETerm.e_any
                                                            FStar_TypeChecker_NBETerm.e_int
                                                            uu____805
                                                            uu____810
                                                            uu____815
                                                           in
                                                        let uu____846 =
                                                          let uu____849 =
                                                            let uu____850 =
                                                              e_tactic_0
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____855 =
                                                              e_tactic_0
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____860 =
                                                              e_tactic_nbe_0
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            let uu____865 =
                                                              e_tactic_nbe_0
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            FStar_Tactics_InterpFuns.mktac2
                                                              (Prims.parse_int "0")
                                                              "__seq"
                                                              FStar_Tactics_Basic.seq
                                                              uu____850
                                                              uu____855
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.seq
                                                              uu____860
                                                              uu____865
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                             in
                                                          let uu____878 =
                                                            let uu____881 =
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
                                                            let uu____882 =
                                                              let uu____885 =
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
                                                              let uu____886 =
                                                                let uu____889
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
                                                                let uu____890
                                                                  =
                                                                  let uu____893
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____896
                                                                     ->
                                                                    fun
                                                                    uu____897
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                  let uu____900
                                                                    =
                                                                    let uu____903
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
                                                                    let uu____904
                                                                    =
                                                                    let uu____907
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
                                                                    let uu____908
                                                                    =
                                                                    let uu____911
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
                                                                    let uu____912
                                                                    =
                                                                    let uu____915
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
                                                                    let uu____916
                                                                    =
                                                                    let uu____919
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
                                                                    let uu____920
                                                                    =
                                                                    let uu____923
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
                                                                    let uu____924
                                                                    =
                                                                    let uu____927
                                                                    =
                                                                    let uu____928
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____933
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____928
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____933
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____942
                                                                    =
                                                                    let uu____945
                                                                    =
                                                                    let uu____946
                                                                    =
                                                                    let uu____958
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____958
                                                                     in
                                                                    let uu____969
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____974
                                                                    =
                                                                    let uu____986
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____986
                                                                     in
                                                                    let uu____997
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____946
                                                                    uu____969
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____974
                                                                    uu____997
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1024
                                                                    =
                                                                    let uu____1027
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
                                                                    let uu____1028
                                                                    =
                                                                    let uu____1031
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
                                                                    let uu____1032
                                                                    =
                                                                    let uu____1035
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
                                                                    let uu____1036
                                                                    =
                                                                    let uu____1039
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
                                                                    let uu____1040
                                                                    =
                                                                    let uu____1043
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
                                                                    let uu____1044
                                                                    =
                                                                    let uu____1047
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
                                                                    let uu____1048
                                                                    =
                                                                    let uu____1051
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
                                                                    let uu____1052
                                                                    =
                                                                    let uu____1055
                                                                    =
                                                                    let uu____1056
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1063
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
                                                                    uu____1056
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1063
                                                                     in
                                                                    let uu____1078
                                                                    =
                                                                    let uu____1081
                                                                    =
                                                                    let uu____1082
                                                                    =
                                                                    let uu____1091
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1091
                                                                     in
                                                                    let uu____1102
                                                                    =
                                                                    let uu____1111
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1111
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1082
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1102
                                                                     in
                                                                    let uu____1134
                                                                    =
                                                                    let uu____1137
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
                                                                    let uu____1138
                                                                    =
                                                                    let uu____1141
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
                                                                    let uu____1142
                                                                    =
                                                                    let uu____1145
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
                                                                    let uu____1146
                                                                    =
                                                                    let uu____1149
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
                                                                    let uu____1150
                                                                    =
                                                                    let uu____1153
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
                                                                    let uu____1154
                                                                    =
                                                                    let uu____1157
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
                                                                    let uu____1158
                                                                    =
                                                                    let uu____1161
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
                                                                    let uu____1162
                                                                    =
                                                                    let uu____1165
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
                                                                    let uu____1166
                                                                    =
                                                                    let uu____1169
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
                                                                    let uu____1170
                                                                    =
                                                                    let uu____1173
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
                                                                    let uu____1174
                                                                    =
                                                                    let uu____1177
                                                                    =
                                                                    let uu____1178
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1183
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1178
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1183
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1192
                                                                    =
                                                                    let uu____1195
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
                                                                    let uu____1196
                                                                    =
                                                                    let uu____1199
                                                                    =
                                                                    let uu____1200
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1205
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1200
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1205
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1214
                                                                    =
                                                                    let uu____1217
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
                                                                    let uu____1218
                                                                    =
                                                                    let uu____1221
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
                                                                    let uu____1222
                                                                    =
                                                                    let uu____1225
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
                                                                    let uu____1226
                                                                    =
                                                                    let uu____1229
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
                                                                    let uu____1230
                                                                    =
                                                                    let uu____1233
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
                                                                    [uu____1233]
                                                                     in
                                                                    uu____1229
                                                                    ::
                                                                    uu____1230
                                                                     in
                                                                    uu____1225
                                                                    ::
                                                                    uu____1226
                                                                     in
                                                                    uu____1221
                                                                    ::
                                                                    uu____1222
                                                                     in
                                                                    uu____1217
                                                                    ::
                                                                    uu____1218
                                                                     in
                                                                    uu____1199
                                                                    ::
                                                                    uu____1214
                                                                     in
                                                                    uu____1195
                                                                    ::
                                                                    uu____1196
                                                                     in
                                                                    uu____1177
                                                                    ::
                                                                    uu____1192
                                                                     in
                                                                    uu____1173
                                                                    ::
                                                                    uu____1174
                                                                     in
                                                                    uu____1169
                                                                    ::
                                                                    uu____1170
                                                                     in
                                                                    uu____1165
                                                                    ::
                                                                    uu____1166
                                                                     in
                                                                    uu____1161
                                                                    ::
                                                                    uu____1162
                                                                     in
                                                                    uu____1157
                                                                    ::
                                                                    uu____1158
                                                                     in
                                                                    uu____1153
                                                                    ::
                                                                    uu____1154
                                                                     in
                                                                    uu____1149
                                                                    ::
                                                                    uu____1150
                                                                     in
                                                                    uu____1145
                                                                    ::
                                                                    uu____1146
                                                                     in
                                                                    uu____1141
                                                                    ::
                                                                    uu____1142
                                                                     in
                                                                    uu____1137
                                                                    ::
                                                                    uu____1138
                                                                     in
                                                                    uu____1081
                                                                    ::
                                                                    uu____1134
                                                                     in
                                                                    uu____1055
                                                                    ::
                                                                    uu____1078
                                                                     in
                                                                    uu____1051
                                                                    ::
                                                                    uu____1052
                                                                     in
                                                                    uu____1047
                                                                    ::
                                                                    uu____1048
                                                                     in
                                                                    uu____1043
                                                                    ::
                                                                    uu____1044
                                                                     in
                                                                    uu____1039
                                                                    ::
                                                                    uu____1040
                                                                     in
                                                                    uu____1035
                                                                    ::
                                                                    uu____1036
                                                                     in
                                                                    uu____1031
                                                                    ::
                                                                    uu____1032
                                                                     in
                                                                    uu____1027
                                                                    ::
                                                                    uu____1028
                                                                     in
                                                                    uu____945
                                                                    ::
                                                                    uu____1024
                                                                     in
                                                                    uu____927
                                                                    ::
                                                                    uu____942
                                                                     in
                                                                    uu____923
                                                                    ::
                                                                    uu____924
                                                                     in
                                                                    uu____919
                                                                    ::
                                                                    uu____920
                                                                     in
                                                                    uu____915
                                                                    ::
                                                                    uu____916
                                                                     in
                                                                    uu____911
                                                                    ::
                                                                    uu____912
                                                                     in
                                                                    uu____907
                                                                    ::
                                                                    uu____908
                                                                     in
                                                                    uu____903
                                                                    ::
                                                                    uu____904
                                                                     in
                                                                  uu____893
                                                                    ::
                                                                    uu____900
                                                                   in
                                                                uu____889 ::
                                                                  uu____890
                                                                 in
                                                              uu____885 ::
                                                                uu____886
                                                               in
                                                            uu____881 ::
                                                              uu____882
                                                             in
                                                          uu____849 ::
                                                            uu____878
                                                           in
                                                        uu____787 ::
                                                          uu____846
                                                         in
                                                      uu____783 :: uu____784
                                                       in
                                                    uu____779 :: uu____780
                                                     in
                                                  uu____775 :: uu____776  in
                                                uu____771 :: uu____772  in
                                              uu____767 :: uu____768  in
                                            uu____763 :: uu____764  in
                                          uu____759 :: uu____760  in
                                        uu____755 :: uu____756  in
                                      uu____751 :: uu____752  in
                                    uu____747 :: uu____748  in
                                  uu____743 :: uu____744  in
                                uu____739 :: uu____740  in
                              uu____721 :: uu____736  in
                            uu____703 :: uu____718  in
                          uu____685 :: uu____700  in
                        uu____659 :: uu____682  in
                      uu____655 :: uu____656  in
                    uu____611 :: uu____652  in
                  uu____607 :: uu____608  in
                uu____599 :: uu____604  in
              uu____539 :: uu____596  in
            set_proofstate_range1 :: uu____536  in
          tracepoint1 :: uu____533  in
        decr_depth1 :: uu____530  in
      incr_depth1 :: uu____527  in
    FStar_List.append uu____524
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
                 let uu____1261 =
                   let uu____1266 =
                     let uu____1267 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____1267]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1266  in
                 uu____1261 FStar_Pervasives_Native.None rng  in
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
               let uu____1320 =
                 let uu____1325 =
                   let uu____1326 =
                     let uu____1335 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1335  in
                   [uu____1326]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1325  in
               uu____1320 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1380 = FStar_Options.tactics_nbe ()  in
               if uu____1380
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____1399 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____1399)
             else ();
             (let result =
                let uu____1402 = primitive_steps ()  in
                norm_f uu____1402 steps
                  proof_state.FStar_Tactics_Types.main_context tm
                 in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____1406 = FStar_Syntax_Print.term_to_string result
                    in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____1406)
              else ();
              (let res =
                 let uu____1413 = FStar_Tactics_Embedding.e_result eb  in
                 FStar_Tactics_InterpFuns.unembed uu____1413 result ncb  in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b,ps)) ->
                   let uu____1428 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1428
                     (fun uu____1432  -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (msg,ps)) ->
                   let uu____1437 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1437
                     (fun uu____1441  -> FStar_Tactics_Basic.fail msg)
               | FStar_Pervasives_Native.None  ->
                   let uu____1444 =
                     let uu____1449 =
                       let uu____1450 =
                         FStar_Syntax_Print.term_to_string result  in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____1450
                        in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____1449)  in
                   FStar_Errors.raise_error uu____1444
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
                 let uu____1480 =
                   let uu____1481 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                   [uu____1481]  in
                 cb f uu____1480  in
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
               let uu____1517 =
                 let uu____1518 =
                   let uu____1523 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1523  in
                 [uu____1518]  in
               cb embedded_tac_b uu____1517  in
             let res =
               let uu____1543 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1543 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1560 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1560
                   (fun uu____1564  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____1569 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1569
                   (fun uu____1573  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____1576 =
                   let uu____1581 =
                     let uu____1582 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1582
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1581)  in
                 FStar_Errors.raise_error uu____1576
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

and unembed_tactic_1_alt :
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
                 let uu____1613 =
                   let uu____1618 =
                     let uu____1619 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____1619]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1618  in
                 uu____1613 FStar_Pervasives_Native.None rng  in
               let app1 = FStar_Syntax_Util.mk_reify app  in
               unembed_tactic_0 er app1 ncb)

and e_tactic_1_alt :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa ->
           FStar_Tactics_Types.proofstate ->
             'Ar FStar_Tactics_Result.__result)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let em uu____1703 uu____1704 uu____1705 uu____1706 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n1 =
        let uu____1774 = unembed_tactic_1_alt ea er t0 n1  in
        match uu____1774 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____1816 = f x  in FStar_Tactics_Basic.run uu____1816))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____1832 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____1832

let report_implicits :
  'Auu____1847 . 'Auu____1847 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____1876 =
               let uu____1877 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____1878 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____1877 uu____1878 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____1876, (imp.FStar_TypeChecker_Env.imp_range))) is
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
            (let uu____1917 = FStar_ST.op_Bang tacdbg  in
             if uu____1917
             then
               let uu____1937 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____1937
             else ());
            (let uu____1939 =
               FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic  in
             match uu____1939 with
             | (uu____1952,uu____1953,g) ->
                 ((let uu____1956 = FStar_ST.op_Bang tacdbg  in
                   if uu____1956 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb
                      in
                   let uu____1982 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____1982 with
                   | (env1,uu____1996) ->
                       let env2 =
                         let uu___353_2002 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___353_2002.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___353_2002.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___353_2002.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___353_2002.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___353_2002.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___353_2002.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___353_2002.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___353_2002.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___353_2002.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___353_2002.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___353_2002.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___353_2002.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___353_2002.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___353_2002.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___353_2002.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___353_2002.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___353_2002.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___353_2002.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___353_2002.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___353_2002.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___353_2002.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___353_2002.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___353_2002.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___353_2002.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___353_2002.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___353_2002.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___353_2002.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___353_2002.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___353_2002.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___353_2002.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___353_2002.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___353_2002.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___353_2002.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___353_2002.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___353_2002.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___353_2002.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___353_2002.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___353_2002.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___353_2002.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___353_2002.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___353_2002.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___354_2004 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___354_2004.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___354_2004.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___354_2004.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___354_2004.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___354_2004.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___354_2004.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___354_2004.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___354_2004.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___354_2004.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___354_2004.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___354_2004.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___354_2004.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___354_2004.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___354_2004.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___354_2004.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___354_2004.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___354_2004.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___354_2004.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___354_2004.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___354_2004.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___354_2004.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___354_2004.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___354_2004.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___354_2004.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___354_2004.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___354_2004.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___354_2004.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___354_2004.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___354_2004.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___354_2004.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___354_2004.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___354_2004.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___354_2004.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___354_2004.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___354_2004.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___354_2004.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___354_2004.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___354_2004.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___354_2004.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___354_2004.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___354_2004.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___355_2006 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___355_2006.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___355_2006.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___355_2006.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___355_2006.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___355_2006.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___355_2006.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___355_2006.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___355_2006.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___355_2006.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___355_2006.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___355_2006.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___355_2006.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___355_2006.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___355_2006.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___355_2006.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___355_2006.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___355_2006.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___355_2006.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___355_2006.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___355_2006.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___355_2006.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___355_2006.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___355_2006.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___355_2006.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___355_2006.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___355_2006.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___355_2006.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___355_2006.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___355_2006.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___355_2006.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___355_2006.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___355_2006.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___355_2006.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___355_2006.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___355_2006.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___355_2006.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___355_2006.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___355_2006.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___355_2006.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___355_2006.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___355_2006.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____2008 = FStar_Range.use_range rng_goal  in
                         let uu____2009 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____2008 uu____2009  in
                       let uu____2010 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____2010 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____2048 = FStar_ST.op_Bang tacdbg  in
                              if uu____2048
                              then
                                let uu____2068 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____2068
                              else ());
                             (let uu____2070 =
                                FStar_Util.record_time
                                  (fun uu____2080  ->
                                     FStar_Tactics_Basic.run_safe tau ps)
                                 in
                              match uu____2070 with
                              | (res,ms) ->
                                  ((let uu____2094 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____2094
                                    then
                                      let uu____2114 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____2115 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____2116 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "}\nTactic %s ran in %s ms (%s)\n"
                                        uu____2114 uu____2115 uu____2116
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____2124,ps1) ->
                                        ((let uu____2127 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2127
                                          then
                                            let uu____2147 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____2147
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____2154 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____2154
                                              then
                                                let uu____2155 =
                                                  let uu____2156 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____2157 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt
                                                    uu____2156 uu____2157
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____2155
                                                 then ()
                                                 else
                                                   (let uu____2159 =
                                                      let uu____2160 =
                                                        let uu____2161 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____2161
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____2160
                                                       in
                                                    failwith uu____2159))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____2164 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2164
                                          then
                                            let uu____2184 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____2184
                                          else ());
                                         (let g1 =
                                            let uu___356_2189 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___356_2189.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___356_2189.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___356_2189.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____2192 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____2192
                                           then
                                             let uu____2212 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits)
                                                in
                                             let uu____2213 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____2212 uu____2213
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____2219 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2219
                                            then
                                              let uu____2239 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits)
                                                 in
                                              let uu____2240 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____2239 uu____2240
                                            else ());
                                           report_implicits ps1
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____2246 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2246
                                            then
                                              let uu____2266 =
                                                let uu____2267 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc
                                                   in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____2267 ps1
                                                 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____2266
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____2274 =
                                            let uu____2275 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____2275 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____2274
                                            "at the time of failure");
                                         (let uu____2276 =
                                            let uu____2281 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____2281)
                                             in
                                          FStar_Errors.raise_error uu____2276
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2293 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2299 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2305 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2360 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2400 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2454 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____2495 . 'Auu____2495 -> 'Auu____2495 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____2523 = FStar_Syntax_Util.head_and_args t  in
        match uu____2523 with
        | (hd1,args) ->
            let uu____2566 =
              let uu____2581 =
                let uu____2582 = FStar_Syntax_Util.un_uinst hd1  in
                uu____2582.FStar_Syntax_Syntax.n  in
              (uu____2581, args)  in
            (match uu____2566 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2597))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2660 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2660 with
                       | (gs,uu____2668) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____2675 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2675 with
                       | (gs,uu____2683) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2726 =
                        let uu____2733 =
                          let uu____2736 =
                            let uu____2737 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2737
                             in
                          [uu____2736]  in
                        (FStar_Syntax_Util.t_true, uu____2733)  in
                      Simplified uu____2726
                  | Both  ->
                      let uu____2748 =
                        let uu____2757 =
                          let uu____2760 =
                            let uu____2761 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2761
                             in
                          [uu____2760]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____2757)  in
                      Dual uu____2748
                  | Neg  -> Simplified (assertion, []))
             | uu____2774 -> Unchanged t)
  
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
    fun uu___348_2864  ->
      match uu___348_2864 with
      | Unchanged t -> let uu____2870 = f t  in Unchanged uu____2870
      | Simplified (t,gs) ->
          let uu____2877 = let uu____2884 = f t  in (uu____2884, gs)  in
          Simplified uu____2877
      | Dual (tn,tp,gs) ->
          let uu____2894 =
            let uu____2903 = f tn  in
            let uu____2904 = f tp  in (uu____2903, uu____2904, gs)  in
          Dual uu____2894
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____2967 = f t1 t2  in Unchanged uu____2967
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____2979 = let uu____2986 = f t1 t2  in (uu____2986, gs)
               in
            Simplified uu____2979
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3000 = let uu____3007 = f t1 t2  in (uu____3007, gs)
               in
            Simplified uu____3000
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3026 =
              let uu____3033 = f t1 t2  in
              (uu____3033, (FStar_List.append gs1 gs2))  in
            Simplified uu____3026
        | uu____3036 ->
            let uu____3045 = explode x  in
            (match uu____3045 with
             | (n1,p1,gs1) ->
                 let uu____3063 = explode y  in
                 (match uu____3063 with
                  | (n2,p2,gs2) ->
                      let uu____3081 =
                        let uu____3090 = f n1 n2  in
                        let uu____3091 = f p1 p2  in
                        (uu____3090, uu____3091, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3081))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3163 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3163
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3211  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3253 =
              let uu____3254 = FStar_Syntax_Subst.compress t  in
              uu____3254.FStar_Syntax_Syntax.n  in
            match uu____3253 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3266 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3266 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3292 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3292 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3312;
                   FStar_Syntax_Syntax.vars = uu____3313;_},(p,uu____3315)::
                 (q,uu____3317)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3373 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3373
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3376 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3376 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3390 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3390.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3394;
                   FStar_Syntax_Syntax.vars = uu____3395;_},(p,uu____3397)::
                 (q,uu____3399)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3455 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3455
                   in
                let xq =
                  let uu____3457 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3457
                   in
                let r1 =
                  let uu____3459 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3459 p  in
                let r2 =
                  let uu____3461 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3461 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3468,Unchanged uu____3469) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3487 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3487.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3490 ->
                     let uu____3499 = explode r1  in
                     (match uu____3499 with
                      | (pn,pp,gs1) ->
                          let uu____3517 = explode r2  in
                          (match uu____3517 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3538 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3541 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3538
                                   uu____3541
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____3605  ->
                       fun r  ->
                         match uu____3605 with
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
                let uu____3757 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____3757 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____3797  ->
                            match uu____3797 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____3819 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___357_3851 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___357_3851.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___357_3851.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____3819 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____3879 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____3879.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____3925 = traverse f pol e t1  in
                let uu____3930 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____3930 uu____3925
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___358_3970 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___358_3970.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___358_3970.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____3977 =
                f pol e
                  (let uu___359_3981 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___359_3981.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___359_3981.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____3977
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___360_3991 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___360_3991.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___360_3991.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____3992 = explode rp  in
              (match uu____3992 with
               | (uu____4001,p',gs') ->
                   Dual
                     ((let uu___361_4011 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___361_4011.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___361_4011.FStar_Syntax_Syntax.vars)
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
      (let uu____4054 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4054);
      (let uu____4075 = FStar_ST.op_Bang tacdbg  in
       if uu____4075
       then
         let uu____4095 =
           let uu____4096 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4096
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4097 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4095
           uu____4097
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4126 =
         let uu____4135 = traverse by_tactic_interp Pos env goal  in
         match uu____4135 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4159 -> failwith "no"  in
       match uu____4126 with
       | (t',gs) ->
           ((let uu____4187 = FStar_ST.op_Bang tacdbg  in
             if uu____4187
             then
               let uu____4207 =
                 let uu____4208 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4208
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4209 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4207 uu____4209
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4257  ->
                    fun g  ->
                      match uu____4257 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4302 =
                              let uu____4305 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____4306 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____4305 uu____4306  in
                            match uu____4302 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4307 =
                                  let uu____4312 =
                                    let uu____4313 =
                                      let uu____4314 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____4314
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____4313
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____4312)
                                   in
                                FStar_Errors.raise_error uu____4307
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4317 = FStar_ST.op_Bang tacdbg  in
                            if uu____4317
                            then
                              let uu____4337 = FStar_Util.string_of_int n1
                                 in
                              let uu____4338 =
                                let uu____4339 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____4339
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4337 uu____4338
                            else ());
                           (let gt' =
                              let uu____4342 =
                                let uu____4343 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4343
                                 in
                              FStar_TypeChecker_Util.label uu____4342
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____4344 =
                              let uu____4353 =
                                let uu____4360 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____4360, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____4353 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____4344)))) s
                 gs
                in
             let uu____4375 = s1  in
             match uu____4375 with
             | (uu____4396,gs1) ->
                 let uu____4414 =
                   let uu____4421 = FStar_Options.peek ()  in
                   (env, t', uu____4421)  in
                 uu____4414 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4434 =
        let uu____4435 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4435  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4434 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4436 =
      let uu____4441 =
        let uu____4442 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4451 =
          let uu____4462 = FStar_Syntax_Syntax.as_arg a  in [uu____4462]  in
        uu____4442 :: uu____4451  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4441  in
    uu____4436 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
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
          let uu____4512 =
            let uu____4517 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____4518 =
              let uu____4519 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4519]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____4517 uu____4518  in
          uu____4512 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____4548 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____4548);
           (let uu____4568 =
              let uu____4575 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____4575 env typ
               in
            match uu____4568 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____4590 =
                        let uu____4593 = FStar_Tactics_Types.goal_env g  in
                        let uu____4594 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____4593 uu____4594  in
                      match uu____4590 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____4597 = FStar_ST.op_Bang tacdbg  in
                            if uu____4597
                            then
                              let uu____4617 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____4617
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____4628 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____4628 guard))
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
        ((let uu____4645 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____4645);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____4666 =
            let uu____4673 = reify_tactic tau  in
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos uu____4673 env typ
             in
          match uu____4666 with
          | (gs,w) ->
              ((let uu____4683 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____4687 =
                         let uu____4688 =
                           let uu____4691 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____4692 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____4691 uu____4692  in
                         FStar_Option.isSome uu____4688  in
                       Prims.op_Negation uu____4687) gs
                   in
                if uu____4683
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
                (let uu____4696 = FStar_ST.op_Bang tacdbg  in
                 if uu____4696
                 then
                   let uu____4716 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____4716
                 else ());
                (let uu____4718 =
                   let uu____4723 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____4723 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____4718 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  