open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec e_tactic_0 :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____327 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____334  ->
         fun uu____335  ->
           fun uu____336  ->
             fun uu____337  -> failwith "Impossible: embedding tactic (0)?")
      (fun t  ->
         fun w  ->
           fun norm1  ->
             let uu____370 = unembed_tactic_0 er t norm1  in
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____370)
      uu____327

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____389 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____399  ->
           fun uu____400  ->
             fun uu____401  ->
               fun uu____402  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  -> fun w  -> unembed_tactic_1 ea er t) uu____389

and e_tactic_nbe_0 :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____440  -> failwith "Impossible: NBE embedding tactic (0)?")
      (fun cb  ->
         fun t  ->
           let uu____456 = unembed_tactic_nbe_0 er cb t  in
           FStar_All.pipe_left
             (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____456)
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
           fun uu____485  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  -> fun t  -> unembed_tactic_nbe_1 ea er cb t)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____506  ->
    let tracepoint1 =
      let uu___349_510 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____511 = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____511;
        FStar_TypeChecker_Cfg.arity =
          (uu___349_510.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___349_510.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___349_510.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___349_510.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___349_510.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___349_510.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___349_510.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let set_proofstate_range1 =
      let uu___350_513 =
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
      let uu____514 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Cfg.name = uu____514;
        FStar_TypeChecker_Cfg.arity =
          (uu___350_513.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___350_513.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___350_513.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___350_513.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___350_513.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___350_513.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___350_513.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let incr_depth1 =
      let uu___351_516 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "incr_depth"
          FStar_Tactics_Types.incr_depth FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.incr_depth
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____517 = FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____517;
        FStar_TypeChecker_Cfg.arity =
          (uu___351_516.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___351_516.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___351_516.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___351_516.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___351_516.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___351_516.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___351_516.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let decr_depth1 =
      let uu___352_519 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "decr_depth"
          FStar_Tactics_Types.decr_depth FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.decr_depth
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____520 = FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____520;
        FStar_TypeChecker_Cfg.arity =
          (uu___352_519.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___352_519.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___352_519.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___352_519.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___352_519.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___352_519.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___352_519.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let uu____521 =
      let uu____524 =
        let uu____527 =
          let uu____530 =
            let uu____533 =
              let uu____536 =
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
              let uu____593 =
                let uu____596 =
                  FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                    "fail" (fun uu____598  -> FStar_Tactics_Basic.fail)
                    FStar_Syntax_Embeddings.e_any
                    FStar_Syntax_Embeddings.e_string
                    FStar_Syntax_Embeddings.e_any
                    (fun uu____600  -> FStar_Tactics_Basic.fail)
                    FStar_TypeChecker_NBETerm.e_any
                    FStar_TypeChecker_NBETerm.e_string
                    FStar_TypeChecker_NBETerm.e_any
                   in
                let uu____601 =
                  let uu____604 =
                    FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                      "trivial" FStar_Tactics_Basic.trivial
                      FStar_Syntax_Embeddings.e_unit
                      FStar_Syntax_Embeddings.e_unit
                      FStar_Tactics_Basic.trivial
                      FStar_TypeChecker_NBETerm.e_unit
                      FStar_TypeChecker_NBETerm.e_unit
                     in
                  let uu____605 =
                    let uu____608 =
                      let uu____609 =
                        e_tactic_0 FStar_Syntax_Embeddings.e_any  in
                      let uu____614 =
                        FStar_Syntax_Embeddings.e_either
                          FStar_Syntax_Embeddings.e_string
                          FStar_Syntax_Embeddings.e_any
                         in
                      let uu____621 =
                        e_tactic_nbe_0 FStar_TypeChecker_NBETerm.e_any  in
                      let uu____626 =
                        FStar_TypeChecker_NBETerm.e_either
                          FStar_TypeChecker_NBETerm.e_string
                          FStar_TypeChecker_NBETerm.e_any
                         in
                      FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                        "__catch"
                        (fun uu____646  -> FStar_Tactics_Basic.catch)
                        FStar_Syntax_Embeddings.e_any uu____609 uu____614
                        (fun uu____648  -> FStar_Tactics_Basic.catch)
                        FStar_TypeChecker_NBETerm.e_any uu____621 uu____626
                       in
                    let uu____649 =
                      let uu____652 =
                        FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                          "intro" FStar_Tactics_Basic.intro
                          FStar_Syntax_Embeddings.e_unit
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Tactics_Basic.intro
                          FStar_TypeChecker_NBETerm.e_unit
                          FStar_Reflection_NBEEmbeddings.e_binder
                         in
                      let uu____653 =
                        let uu____656 =
                          let uu____657 =
                            FStar_Syntax_Embeddings.e_tuple2
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder
                             in
                          let uu____664 =
                            FStar_TypeChecker_NBETerm.e_tuple2
                              FStar_Reflection_NBEEmbeddings.e_binder
                              FStar_Reflection_NBEEmbeddings.e_binder
                             in
                          FStar_Tactics_InterpFuns.mktac1
                            (Prims.parse_int "0") "intro_rec"
                            FStar_Tactics_Basic.intro_rec
                            FStar_Syntax_Embeddings.e_unit uu____657
                            FStar_Tactics_Basic.intro_rec
                            FStar_TypeChecker_NBETerm.e_unit uu____664
                           in
                        let uu____679 =
                          let uu____682 =
                            let uu____683 =
                              FStar_Syntax_Embeddings.e_list
                                FStar_Syntax_Embeddings.e_norm_step
                               in
                            let uu____688 =
                              FStar_TypeChecker_NBETerm.e_list
                                FStar_TypeChecker_NBETerm.e_norm_step
                               in
                            FStar_Tactics_InterpFuns.mktac1
                              (Prims.parse_int "0") "norm"
                              FStar_Tactics_Basic.norm uu____683
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Tactics_Basic.norm uu____688
                              FStar_TypeChecker_NBETerm.e_unit
                             in
                          let uu____697 =
                            let uu____700 =
                              let uu____701 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_norm_step
                                 in
                              let uu____706 =
                                FStar_TypeChecker_NBETerm.e_list
                                  FStar_TypeChecker_NBETerm.e_norm_step
                                 in
                              FStar_Tactics_InterpFuns.mktac3
                                (Prims.parse_int "0") "norm_term_env"
                                FStar_Tactics_Basic.norm_term_env
                                FStar_Reflection_Embeddings.e_env uu____701
                                FStar_Reflection_Embeddings.e_term
                                FStar_Reflection_Embeddings.e_term
                                FStar_Tactics_Basic.norm_term_env
                                FStar_Reflection_NBEEmbeddings.e_env
                                uu____706
                                FStar_Reflection_NBEEmbeddings.e_term
                                FStar_Reflection_NBEEmbeddings.e_term
                               in
                            let uu____715 =
                              let uu____718 =
                                let uu____719 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Syntax_Embeddings.e_norm_step
                                   in
                                let uu____724 =
                                  FStar_TypeChecker_NBETerm.e_list
                                    FStar_TypeChecker_NBETerm.e_norm_step
                                   in
                                FStar_Tactics_InterpFuns.mktac2
                                  (Prims.parse_int "0") "norm_binder_type"
                                  FStar_Tactics_Basic.norm_binder_type
                                  uu____719
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Tactics_Basic.norm_binder_type
                                  uu____724
                                  FStar_Reflection_NBEEmbeddings.e_binder
                                  FStar_TypeChecker_NBETerm.e_unit
                                 in
                              let uu____733 =
                                let uu____736 =
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
                                let uu____737 =
                                  let uu____740 =
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "binder_retype"
                                      FStar_Tactics_Basic.binder_retype
                                      FStar_Reflection_Embeddings.e_binder
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.binder_retype
                                      FStar_Reflection_NBEEmbeddings.e_binder
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____741 =
                                    let uu____744 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        (Prims.parse_int "0") "revert"
                                        FStar_Tactics_Basic.revert
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.revert
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____745 =
                                      let uu____748 =
                                        FStar_Tactics_InterpFuns.mktac1
                                          (Prims.parse_int "0") "clear_top"
                                          FStar_Tactics_Basic.clear_top
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Tactics_Basic.clear_top
                                          FStar_TypeChecker_NBETerm.e_unit
                                          FStar_TypeChecker_NBETerm.e_unit
                                         in
                                      let uu____749 =
                                        let uu____752 =
                                          FStar_Tactics_InterpFuns.mktac1
                                            (Prims.parse_int "0") "clear"
                                            FStar_Tactics_Basic.clear
                                            FStar_Reflection_Embeddings.e_binder
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_Tactics_Basic.clear
                                            FStar_Reflection_NBEEmbeddings.e_binder
                                            FStar_TypeChecker_NBETerm.e_unit
                                           in
                                        let uu____753 =
                                          let uu____756 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              (Prims.parse_int "0") "rewrite"
                                              FStar_Tactics_Basic.rewrite
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Tactics_Basic.rewrite
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                              FStar_TypeChecker_NBETerm.e_unit
                                             in
                                          let uu____757 =
                                            let uu____760 =
                                              FStar_Tactics_InterpFuns.mktac1
                                                (Prims.parse_int "0") "smt"
                                                FStar_Tactics_Basic.smt
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Tactics_Basic.smt
                                                FStar_TypeChecker_NBETerm.e_unit
                                                FStar_TypeChecker_NBETerm.e_unit
                                               in
                                            let uu____761 =
                                              let uu____764 =
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
                                              let uu____765 =
                                                let uu____768 =
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
                                                let uu____769 =
                                                  let uu____772 =
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
                                                  let uu____773 =
                                                    let uu____776 =
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
                                                    let uu____777 =
                                                      let uu____780 =
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
                                                      let uu____781 =
                                                        let uu____784 =
                                                          let uu____785 =
                                                            e_tactic_0
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____790 =
                                                            e_tactic_0
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____795 =
                                                            FStar_Syntax_Embeddings.e_tuple2
                                                              FStar_Syntax_Embeddings.e_any
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____802 =
                                                            e_tactic_nbe_0
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          let uu____807 =
                                                            e_tactic_nbe_0
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          let uu____812 =
                                                            FStar_TypeChecker_NBETerm.e_tuple2
                                                              FStar_TypeChecker_NBETerm.e_any
                                                              FStar_TypeChecker_NBETerm.e_any
                                                             in
                                                          FStar_Tactics_InterpFuns.mktac5
                                                            (Prims.parse_int "2")
                                                            "__divide"
                                                            (fun uu____837 
                                                               ->
                                                               fun uu____838 
                                                                 ->
                                                                 FStar_Tactics_Basic.divide)
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Syntax_Embeddings.e_int
                                                            uu____785
                                                            uu____790
                                                            uu____795
                                                            (fun uu____841 
                                                               ->
                                                               fun uu____842 
                                                                 ->
                                                                 FStar_Tactics_Basic.divide)
                                                            FStar_TypeChecker_NBETerm.e_any
                                                            FStar_TypeChecker_NBETerm.e_any
                                                            FStar_TypeChecker_NBETerm.e_int
                                                            uu____802
                                                            uu____807
                                                            uu____812
                                                           in
                                                        let uu____843 =
                                                          let uu____846 =
                                                            let uu____847 =
                                                              e_tactic_0
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____852 =
                                                              e_tactic_0
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____857 =
                                                              e_tactic_nbe_0
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            let uu____862 =
                                                              e_tactic_nbe_0
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            FStar_Tactics_InterpFuns.mktac2
                                                              (Prims.parse_int "0")
                                                              "__seq"
                                                              FStar_Tactics_Basic.seq
                                                              uu____847
                                                              uu____852
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.seq
                                                              uu____857
                                                              uu____862
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                             in
                                                          let uu____875 =
                                                            let uu____878 =
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
                                                            let uu____879 =
                                                              let uu____882 =
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
                                                              let uu____883 =
                                                                let uu____886
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
                                                                let uu____887
                                                                  =
                                                                  let uu____890
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____893
                                                                     ->
                                                                    fun
                                                                    uu____894
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                  let uu____897
                                                                    =
                                                                    let uu____900
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
                                                                    let uu____901
                                                                    =
                                                                    let uu____904
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
                                                                    let uu____905
                                                                    =
                                                                    let uu____908
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
                                                                    let uu____909
                                                                    =
                                                                    let uu____912
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
                                                                    let uu____913
                                                                    =
                                                                    let uu____916
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
                                                                    let uu____917
                                                                    =
                                                                    let uu____920
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
                                                                    let uu____921
                                                                    =
                                                                    let uu____924
                                                                    =
                                                                    let uu____925
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____930
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____925
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____930
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____939
                                                                    =
                                                                    let uu____942
                                                                    =
                                                                    let uu____943
                                                                    =
                                                                    let uu____955
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____955
                                                                     in
                                                                    let uu____966
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____971
                                                                    =
                                                                    let uu____983
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____983
                                                                     in
                                                                    let uu____994
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____943
                                                                    uu____966
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____971
                                                                    uu____994
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1021
                                                                    =
                                                                    let uu____1024
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
                                                                    let uu____1025
                                                                    =
                                                                    let uu____1028
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
                                                                    let uu____1029
                                                                    =
                                                                    let uu____1032
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
                                                                    let uu____1033
                                                                    =
                                                                    let uu____1036
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
                                                                    let uu____1037
                                                                    =
                                                                    let uu____1040
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
                                                                    let uu____1041
                                                                    =
                                                                    let uu____1044
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
                                                                    let uu____1045
                                                                    =
                                                                    let uu____1048
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
                                                                    let uu____1049
                                                                    =
                                                                    let uu____1052
                                                                    =
                                                                    let uu____1053
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1060
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
                                                                    uu____1053
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1060
                                                                     in
                                                                    let uu____1075
                                                                    =
                                                                    let uu____1078
                                                                    =
                                                                    let uu____1079
                                                                    =
                                                                    let uu____1088
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1088
                                                                     in
                                                                    let uu____1099
                                                                    =
                                                                    let uu____1108
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1108
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1079
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1099
                                                                     in
                                                                    let uu____1131
                                                                    =
                                                                    let uu____1134
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
                                                                    let uu____1135
                                                                    =
                                                                    let uu____1138
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
                                                                    let uu____1139
                                                                    =
                                                                    let uu____1142
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
                                                                    let uu____1143
                                                                    =
                                                                    let uu____1146
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
                                                                    let uu____1147
                                                                    =
                                                                    let uu____1150
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
                                                                    let uu____1151
                                                                    =
                                                                    let uu____1154
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
                                                                    let uu____1155
                                                                    =
                                                                    let uu____1158
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
                                                                    let uu____1159
                                                                    =
                                                                    let uu____1162
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
                                                                    let uu____1163
                                                                    =
                                                                    let uu____1166
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
                                                                    let uu____1167
                                                                    =
                                                                    let uu____1170
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
                                                                    let uu____1171
                                                                    =
                                                                    let uu____1174
                                                                    =
                                                                    let uu____1175
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1180
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1175
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1180
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1189
                                                                    =
                                                                    let uu____1192
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
                                                                    let uu____1193
                                                                    =
                                                                    let uu____1196
                                                                    =
                                                                    let uu____1197
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1202
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1197
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1202
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1211
                                                                    =
                                                                    let uu____1214
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
                                                                    let uu____1215
                                                                    =
                                                                    let uu____1218
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
                                                                    let uu____1219
                                                                    =
                                                                    let uu____1222
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
                                                                    let uu____1223
                                                                    =
                                                                    let uu____1226
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
                                                                    let uu____1227
                                                                    =
                                                                    let uu____1230
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
                                                                    [uu____1230]
                                                                     in
                                                                    uu____1226
                                                                    ::
                                                                    uu____1227
                                                                     in
                                                                    uu____1222
                                                                    ::
                                                                    uu____1223
                                                                     in
                                                                    uu____1218
                                                                    ::
                                                                    uu____1219
                                                                     in
                                                                    uu____1214
                                                                    ::
                                                                    uu____1215
                                                                     in
                                                                    uu____1196
                                                                    ::
                                                                    uu____1211
                                                                     in
                                                                    uu____1192
                                                                    ::
                                                                    uu____1193
                                                                     in
                                                                    uu____1174
                                                                    ::
                                                                    uu____1189
                                                                     in
                                                                    uu____1170
                                                                    ::
                                                                    uu____1171
                                                                     in
                                                                    uu____1166
                                                                    ::
                                                                    uu____1167
                                                                     in
                                                                    uu____1162
                                                                    ::
                                                                    uu____1163
                                                                     in
                                                                    uu____1158
                                                                    ::
                                                                    uu____1159
                                                                     in
                                                                    uu____1154
                                                                    ::
                                                                    uu____1155
                                                                     in
                                                                    uu____1150
                                                                    ::
                                                                    uu____1151
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
                                                                    uu____1078
                                                                    ::
                                                                    uu____1131
                                                                     in
                                                                    uu____1052
                                                                    ::
                                                                    uu____1075
                                                                     in
                                                                    uu____1048
                                                                    ::
                                                                    uu____1049
                                                                     in
                                                                    uu____1044
                                                                    ::
                                                                    uu____1045
                                                                     in
                                                                    uu____1040
                                                                    ::
                                                                    uu____1041
                                                                     in
                                                                    uu____1036
                                                                    ::
                                                                    uu____1037
                                                                     in
                                                                    uu____1032
                                                                    ::
                                                                    uu____1033
                                                                     in
                                                                    uu____1028
                                                                    ::
                                                                    uu____1029
                                                                     in
                                                                    uu____1024
                                                                    ::
                                                                    uu____1025
                                                                     in
                                                                    uu____942
                                                                    ::
                                                                    uu____1021
                                                                     in
                                                                    uu____924
                                                                    ::
                                                                    uu____939
                                                                     in
                                                                    uu____920
                                                                    ::
                                                                    uu____921
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
                                                                  uu____890
                                                                    ::
                                                                    uu____897
                                                                   in
                                                                uu____886 ::
                                                                  uu____887
                                                                 in
                                                              uu____882 ::
                                                                uu____883
                                                               in
                                                            uu____878 ::
                                                              uu____879
                                                             in
                                                          uu____846 ::
                                                            uu____875
                                                           in
                                                        uu____784 ::
                                                          uu____843
                                                         in
                                                      uu____780 :: uu____781
                                                       in
                                                    uu____776 :: uu____777
                                                     in
                                                  uu____772 :: uu____773  in
                                                uu____768 :: uu____769  in
                                              uu____764 :: uu____765  in
                                            uu____760 :: uu____761  in
                                          uu____756 :: uu____757  in
                                        uu____752 :: uu____753  in
                                      uu____748 :: uu____749  in
                                    uu____744 :: uu____745  in
                                  uu____740 :: uu____741  in
                                uu____736 :: uu____737  in
                              uu____718 :: uu____733  in
                            uu____700 :: uu____715  in
                          uu____682 :: uu____697  in
                        uu____656 :: uu____679  in
                      uu____652 :: uu____653  in
                    uu____608 :: uu____649  in
                  uu____604 :: uu____605  in
                uu____596 :: uu____601  in
              uu____536 :: uu____593  in
            set_proofstate_range1 :: uu____533  in
          tracepoint1 :: uu____530  in
        decr_depth1 :: uu____527  in
      incr_depth1 :: uu____524  in
    FStar_List.append uu____521
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
                 let uu____1258 =
                   let uu____1263 =
                     let uu____1264 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____1264]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1263  in
                 uu____1258 FStar_Pervasives_Native.None rng  in
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
               let uu____1317 =
                 let uu____1322 =
                   let uu____1323 =
                     let uu____1332 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1332  in
                   [uu____1323]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1322  in
               uu____1317 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1377 = FStar_Options.tactics_nbe ()  in
               if uu____1377
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____1396 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____1396)
             else ();
             (let result =
                let uu____1399 = primitive_steps ()  in
                norm_f uu____1399 steps
                  proof_state.FStar_Tactics_Types.main_context tm
                 in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____1403 = FStar_Syntax_Print.term_to_string result
                    in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____1403)
              else ();
              (let res =
                 let uu____1410 = FStar_Tactics_Embedding.e_result eb  in
                 FStar_Tactics_InterpFuns.unembed uu____1410 result ncb  in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b,ps)) ->
                   let uu____1425 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1425
                     (fun uu____1429  -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (msg,ps)) ->
                   let uu____1434 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1434
                     (fun uu____1438  -> FStar_Tactics_Basic.fail msg)
               | FStar_Pervasives_Native.None  ->
                   let uu____1441 =
                     let uu____1446 =
                       let uu____1447 =
                         FStar_Syntax_Print.term_to_string result  in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____1447
                        in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____1446)  in
                   FStar_Errors.raise_error uu____1441
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
                 let uu____1477 =
                   let uu____1478 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                   [uu____1478]  in
                 cb f uu____1477  in
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
               let uu____1514 =
                 let uu____1515 =
                   let uu____1520 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1520  in
                 [uu____1515]  in
               cb embedded_tac_b uu____1514  in
             let res =
               let uu____1540 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1540 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1557 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1557
                   (fun uu____1561  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____1566 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1566
                   (fun uu____1570  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____1573 =
                   let uu____1578 =
                     let uu____1579 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1579
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1578)  in
                 FStar_Errors.raise_error uu____1573
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
                 let uu____1610 =
                   let uu____1615 =
                     let uu____1616 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____1616]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1615  in
                 uu____1610 FStar_Pervasives_Native.None rng  in
               let app1 = FStar_Syntax_Util.mk_reify app  in
               unembed_tactic_0 er app1 ncb)

and e_tactic_1_alt :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____1654 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____1664  ->
           fun uu____1665  ->
             fun uu____1666  ->
               fun uu____1667  ->
                 failwith "Impossible: embedding tactic (1)?")
        (fun t  -> fun w  -> unembed_tactic_1_alt ea er t) uu____1654

let report_implicits :
  'Auu____1703 . 'Auu____1703 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____1732 =
               let uu____1733 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____1734 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____1733 uu____1734 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____1732, (imp.FStar_TypeChecker_Env.imp_range))) is
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
            (let uu____1773 = FStar_ST.op_Bang tacdbg  in
             if uu____1773
             then
               let uu____1793 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____1793
             else ());
            (let uu____1795 =
               FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic  in
             match uu____1795 with
             | (uu____1808,uu____1809,g) ->
                 ((let uu____1812 = FStar_ST.op_Bang tacdbg  in
                   if uu____1812 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb
                      in
                   let uu____1838 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____1838 with
                   | (env1,uu____1852) ->
                       let env2 =
                         let uu___353_1858 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___353_1858.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___353_1858.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___353_1858.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___353_1858.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___353_1858.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___353_1858.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___353_1858.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___353_1858.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___353_1858.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___353_1858.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___353_1858.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___353_1858.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___353_1858.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___353_1858.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___353_1858.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___353_1858.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___353_1858.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___353_1858.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___353_1858.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___353_1858.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___353_1858.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___353_1858.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___353_1858.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___353_1858.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___353_1858.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___353_1858.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___353_1858.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___353_1858.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___353_1858.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___353_1858.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___353_1858.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___353_1858.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___353_1858.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___353_1858.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___353_1858.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___353_1858.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___353_1858.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___353_1858.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___353_1858.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___353_1858.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___353_1858.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___354_1860 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___354_1860.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___354_1860.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___354_1860.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___354_1860.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___354_1860.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___354_1860.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___354_1860.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___354_1860.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___354_1860.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___354_1860.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___354_1860.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___354_1860.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___354_1860.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___354_1860.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___354_1860.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___354_1860.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___354_1860.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___354_1860.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___354_1860.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___354_1860.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___354_1860.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___354_1860.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___354_1860.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___354_1860.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___354_1860.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___354_1860.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___354_1860.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___354_1860.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___354_1860.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___354_1860.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___354_1860.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___354_1860.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___354_1860.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___354_1860.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___354_1860.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___354_1860.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___354_1860.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___354_1860.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___354_1860.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___354_1860.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___354_1860.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___355_1862 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___355_1862.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___355_1862.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___355_1862.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___355_1862.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___355_1862.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___355_1862.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___355_1862.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___355_1862.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___355_1862.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___355_1862.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___355_1862.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___355_1862.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___355_1862.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___355_1862.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___355_1862.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___355_1862.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___355_1862.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___355_1862.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___355_1862.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___355_1862.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___355_1862.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___355_1862.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___355_1862.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___355_1862.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___355_1862.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___355_1862.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___355_1862.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___355_1862.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___355_1862.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___355_1862.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___355_1862.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___355_1862.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___355_1862.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___355_1862.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___355_1862.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___355_1862.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___355_1862.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___355_1862.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___355_1862.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___355_1862.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___355_1862.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____1864 = FStar_Range.use_range rng_goal  in
                         let uu____1865 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____1864 uu____1865  in
                       let uu____1866 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____1866 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____1904 = FStar_ST.op_Bang tacdbg  in
                              if uu____1904
                              then
                                let uu____1924 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____1924
                              else ());
                             (let uu____1926 =
                                FStar_Util.record_time
                                  (fun uu____1936  ->
                                     FStar_Tactics_Basic.run_safe tau ps)
                                 in
                              match uu____1926 with
                              | (res,ms) ->
                                  ((let uu____1950 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____1950
                                    then
                                      let uu____1970 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____1971 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____1972 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "}\nTactic %s ran in %s ms (%s)\n"
                                        uu____1970 uu____1971 uu____1972
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____1980,ps1) ->
                                        ((let uu____1983 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1983
                                          then
                                            let uu____2003 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____2003
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____2010 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____2010
                                              then
                                                let uu____2011 =
                                                  let uu____2012 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____2013 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt
                                                    uu____2012 uu____2013
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____2011
                                                 then ()
                                                 else
                                                   (let uu____2015 =
                                                      let uu____2016 =
                                                        let uu____2017 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____2017
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____2016
                                                       in
                                                    failwith uu____2015))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____2020 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2020
                                          then
                                            let uu____2040 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____2040
                                          else ());
                                         (let g1 =
                                            let uu___356_2045 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___356_2045.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___356_2045.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___356_2045.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____2048 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____2048
                                           then
                                             let uu____2068 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits)
                                                in
                                             let uu____2069 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____2068 uu____2069
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____2075 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2075
                                            then
                                              let uu____2095 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits)
                                                 in
                                              let uu____2096 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____2095 uu____2096
                                            else ());
                                           report_implicits ps1
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____2102 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2102
                                            then
                                              let uu____2122 =
                                                let uu____2123 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc
                                                   in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____2123 ps1
                                                 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____2122
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____2130 =
                                            let uu____2131 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____2131 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____2130
                                            "at the time of failure");
                                         (let uu____2132 =
                                            let uu____2137 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____2137)
                                             in
                                          FStar_Errors.raise_error uu____2132
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2149 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2155 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2161 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2216 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2256 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2310 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____2351 . 'Auu____2351 -> 'Auu____2351 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____2379 = FStar_Syntax_Util.head_and_args t  in
        match uu____2379 with
        | (hd1,args) ->
            let uu____2422 =
              let uu____2437 =
                let uu____2438 = FStar_Syntax_Util.un_uinst hd1  in
                uu____2438.FStar_Syntax_Syntax.n  in
              (uu____2437, args)  in
            (match uu____2422 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2453))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2516 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2516 with
                       | (gs,uu____2524) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____2531 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2531 with
                       | (gs,uu____2539) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2582 =
                        let uu____2589 =
                          let uu____2592 =
                            let uu____2593 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2593
                             in
                          [uu____2592]  in
                        (FStar_Syntax_Util.t_true, uu____2589)  in
                      Simplified uu____2582
                  | Both  ->
                      let uu____2604 =
                        let uu____2613 =
                          let uu____2616 =
                            let uu____2617 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2617
                             in
                          [uu____2616]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____2613)  in
                      Dual uu____2604
                  | Neg  -> Simplified (assertion, []))
             | uu____2630 -> Unchanged t)
  
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
    fun uu___348_2720  ->
      match uu___348_2720 with
      | Unchanged t -> let uu____2726 = f t  in Unchanged uu____2726
      | Simplified (t,gs) ->
          let uu____2733 = let uu____2740 = f t  in (uu____2740, gs)  in
          Simplified uu____2733
      | Dual (tn,tp,gs) ->
          let uu____2750 =
            let uu____2759 = f tn  in
            let uu____2760 = f tp  in (uu____2759, uu____2760, gs)  in
          Dual uu____2750
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____2823 = f t1 t2  in Unchanged uu____2823
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____2835 = let uu____2842 = f t1 t2  in (uu____2842, gs)
               in
            Simplified uu____2835
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____2856 = let uu____2863 = f t1 t2  in (uu____2863, gs)
               in
            Simplified uu____2856
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____2882 =
              let uu____2889 = f t1 t2  in
              (uu____2889, (FStar_List.append gs1 gs2))  in
            Simplified uu____2882
        | uu____2892 ->
            let uu____2901 = explode x  in
            (match uu____2901 with
             | (n1,p1,gs1) ->
                 let uu____2919 = explode y  in
                 (match uu____2919 with
                  | (n2,p2,gs2) ->
                      let uu____2937 =
                        let uu____2946 = f n1 n2  in
                        let uu____2947 = f p1 p2  in
                        (uu____2946, uu____2947, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____2937))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3019 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3019
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3067  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3109 =
              let uu____3110 = FStar_Syntax_Subst.compress t  in
              uu____3110.FStar_Syntax_Syntax.n  in
            match uu____3109 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3122 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3122 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3148 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3148 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3168;
                   FStar_Syntax_Syntax.vars = uu____3169;_},(p,uu____3171)::
                 (q,uu____3173)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3229 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3229
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3232 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3232 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3246 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3246.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3250;
                   FStar_Syntax_Syntax.vars = uu____3251;_},(p,uu____3253)::
                 (q,uu____3255)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3311 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3311
                   in
                let xq =
                  let uu____3313 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3313
                   in
                let r1 =
                  let uu____3315 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3315 p  in
                let r2 =
                  let uu____3317 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3317 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3324,Unchanged uu____3325) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3343 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3343.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3346 ->
                     let uu____3355 = explode r1  in
                     (match uu____3355 with
                      | (pn,pp,gs1) ->
                          let uu____3373 = explode r2  in
                          (match uu____3373 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3394 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3397 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3394
                                   uu____3397
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____3461  ->
                       fun r  ->
                         match uu____3461 with
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
                let uu____3613 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____3613 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____3653  ->
                            match uu____3653 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____3675 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___357_3707 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___357_3707.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___357_3707.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____3675 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____3735 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____3735.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____3781 = traverse f pol e t1  in
                let uu____3786 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____3786 uu____3781
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___358_3826 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___358_3826.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___358_3826.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____3833 =
                f pol e
                  (let uu___359_3837 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___359_3837.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___359_3837.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____3833
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___360_3847 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___360_3847.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___360_3847.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____3848 = explode rp  in
              (match uu____3848 with
               | (uu____3857,p',gs') ->
                   Dual
                     ((let uu___361_3867 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___361_3867.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___361_3867.FStar_Syntax_Syntax.vars)
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
      (let uu____3910 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____3910);
      (let uu____3931 = FStar_ST.op_Bang tacdbg  in
       if uu____3931
       then
         let uu____3951 =
           let uu____3952 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____3952
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____3953 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3951
           uu____3953
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____3982 =
         let uu____3991 = traverse by_tactic_interp Pos env goal  in
         match uu____3991 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4015 -> failwith "no"  in
       match uu____3982 with
       | (t',gs) ->
           ((let uu____4043 = FStar_ST.op_Bang tacdbg  in
             if uu____4043
             then
               let uu____4063 =
                 let uu____4064 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4064
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4065 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4063 uu____4065
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4113  ->
                    fun g  ->
                      match uu____4113 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4158 =
                              let uu____4161 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____4162 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____4161 uu____4162  in
                            match uu____4158 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4163 =
                                  let uu____4168 =
                                    let uu____4169 =
                                      let uu____4170 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____4170
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____4169
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____4168)
                                   in
                                FStar_Errors.raise_error uu____4163
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4173 = FStar_ST.op_Bang tacdbg  in
                            if uu____4173
                            then
                              let uu____4193 = FStar_Util.string_of_int n1
                                 in
                              let uu____4194 =
                                let uu____4195 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____4195
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4193 uu____4194
                            else ());
                           (let gt' =
                              let uu____4198 =
                                let uu____4199 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4199
                                 in
                              FStar_TypeChecker_Util.label uu____4198
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____4200 =
                              let uu____4209 =
                                let uu____4216 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____4216, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____4209 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____4200)))) s
                 gs
                in
             let uu____4231 = s1  in
             match uu____4231 with
             | (uu____4252,gs1) ->
                 let uu____4270 =
                   let uu____4277 = FStar_Options.peek ()  in
                   (env, t', uu____4277)  in
                 uu____4270 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4290 =
        let uu____4291 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4291  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4290 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4292 =
      let uu____4297 =
        let uu____4298 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4307 =
          let uu____4318 = FStar_Syntax_Syntax.as_arg a  in [uu____4318]  in
        uu____4298 :: uu____4307  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4297  in
    uu____4292 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
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
          let uu____4368 =
            let uu____4373 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____4374 =
              let uu____4375 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4375]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____4373 uu____4374  in
          uu____4368 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____4404 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____4404);
           (let uu____4424 =
              let uu____4431 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____4431 env typ
               in
            match uu____4424 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____4446 =
                        let uu____4449 = FStar_Tactics_Types.goal_env g  in
                        let uu____4450 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____4449 uu____4450  in
                      match uu____4446 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____4453 = FStar_ST.op_Bang tacdbg  in
                            if uu____4453
                            then
                              let uu____4473 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____4473
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____4484 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____4484 guard))
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
        ((let uu____4501 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____4501);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____4522 =
            let uu____4529 = reify_tactic tau  in
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos uu____4529 env typ
             in
          match uu____4522 with
          | (gs,w) ->
              ((let uu____4539 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____4543 =
                         let uu____4544 =
                           let uu____4547 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____4548 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____4547 uu____4548  in
                         FStar_Option.isSome uu____4544  in
                       Prims.op_Negation uu____4543) gs
                   in
                if uu____4539
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
                (let uu____4552 = FStar_ST.op_Bang tacdbg  in
                 if uu____4552
                 then
                   let uu____4572 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____4572
                 else ());
                (let uu____4574 =
                   let uu____4579 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____4579 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____4574 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  