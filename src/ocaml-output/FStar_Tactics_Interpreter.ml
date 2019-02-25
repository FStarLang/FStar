open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let mktot1' :
  'Auu____73659 'Auu____73660 'Auu____73661 'Auu____73662 .
    Prims.int ->
      Prims.string ->
        ('Auu____73659 -> 'Auu____73660) ->
          'Auu____73659 FStar_Syntax_Embeddings.embedding ->
            'Auu____73660 FStar_Syntax_Embeddings.embedding ->
              ('Auu____73661 -> 'Auu____73662) ->
                'Auu____73661 FStar_TypeChecker_NBETerm.embedding ->
                  'Auu____73662 FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity  ->
    fun nm  ->
      fun f  ->
        fun ea  ->
          fun er  ->
            fun nf  ->
              fun ena  ->
                fun enr  ->
                  let uu___622_73733 =
                    FStar_Tactics_InterpFuns.mktot1 uarity nm f ea er nf ena
                      enr
                     in
                  let uu____73734 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____73734;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___622_73733.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___622_73733.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___622_73733.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___622_73733.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___622_73733.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___622_73733.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___622_73733.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot2' :
  'Auu____73769 'Auu____73770 'Auu____73771 'Auu____73772 'Auu____73773
    'Auu____73774 .
    Prims.int ->
      Prims.string ->
        ('Auu____73769 -> 'Auu____73770 -> 'Auu____73771) ->
          'Auu____73769 FStar_Syntax_Embeddings.embedding ->
            'Auu____73770 FStar_Syntax_Embeddings.embedding ->
              'Auu____73771 FStar_Syntax_Embeddings.embedding ->
                ('Auu____73772 -> 'Auu____73773 -> 'Auu____73774) ->
                  'Auu____73772 FStar_TypeChecker_NBETerm.embedding ->
                    'Auu____73773 FStar_TypeChecker_NBETerm.embedding ->
                      'Auu____73774 FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity  ->
    fun nm  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun er  ->
              fun nf  ->
                fun ena  ->
                  fun enb  ->
                    fun enr  ->
                      let uu___634_73873 =
                        FStar_Tactics_InterpFuns.mktot2 uarity nm f ea eb er
                          nf ena enb enr
                         in
                      let uu____73874 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm)
                         in
                      {
                        FStar_TypeChecker_Cfg.name = uu____73874;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___634_73873.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___634_73873.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___634_73873.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___634_73873.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___634_73873.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___634_73873.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___634_73873.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
  
let rec e_tactic_thunk :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____74183 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____74190  ->
         fun uu____74191  ->
           fun uu____74192  ->
             fun uu____74193  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____74228 =
               let uu____74231 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____74231 ()  in
             FStar_Pervasives_Native.Some uu____74228) uu____74183

and e_tactic_nbe_thunk :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____74245 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____74251  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____74260 =
             let uu____74263 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____74263 ()  in
           FStar_Pervasives_Native.Some uu____74260)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____74245

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____74278 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____74288  ->
           fun uu____74289  ->
             fun uu____74290  ->
               fun uu____74291  ->
                 failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____74328 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____74328) uu____74278

and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____74348 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____74357  ->
             failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____74368 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____74368)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____74348

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____74380  ->
    let uu____74383 =
      let uu____74386 =
        mktot1' (Prims.parse_int "0") "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____74389 =
        let uu____74392 =
          mktot2' (Prims.parse_int "0") "set_proofstate_range"
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Syntax_Embeddings.e_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_TypeChecker_NBETerm.e_range
            FStar_Tactics_Embedding.e_proofstate_nbe
           in
        let uu____74395 =
          let uu____74398 =
            mktot1' (Prims.parse_int "0") "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe
             in
          let uu____74401 =
            let uu____74404 =
              mktot1' (Prims.parse_int "0") "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____74407 =
              let uu____74410 =
                let uu____74411 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal
                   in
                let uu____74416 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe
                   in
                mktot1' (Prims.parse_int "0") "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____74411
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____74416
                 in
              let uu____74427 =
                let uu____74430 =
                  let uu____74431 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____74436 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mktot1' (Prims.parse_int "0") "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____74431
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____74436
                   in
                let uu____74447 =
                  let uu____74450 =
                    mktot1' (Prims.parse_int "0") "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env
                     in
                  let uu____74453 =
                    let uu____74456 =
                      mktot1' (Prims.parse_int "0") "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term
                       in
                    let uu____74459 =
                      let uu____74462 =
                        mktot1' (Prims.parse_int "0") "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____74465 =
                        let uu____74468 =
                          mktot1' (Prims.parse_int "0") "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool
                           in
                        let uu____74473 =
                          let uu____74476 =
                            mktot1' (Prims.parse_int "0") "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string
                             in
                          let uu____74481 =
                            let uu____74484 =
                              mktot2' (Prims.parse_int "0") "set_label"
                                FStar_Tactics_Types.set_label
                                FStar_Syntax_Embeddings.e_string
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Types.set_label
                                FStar_TypeChecker_NBETerm.e_string
                                FStar_Tactics_Embedding.e_goal_nbe
                                FStar_Tactics_Embedding.e_goal_nbe
                               in
                            let uu____74489 =
                              let uu____74492 =
                                FStar_Tactics_InterpFuns.mktot2
                                  (Prims.parse_int "0") "push_binder"
                                  (fun env  ->
                                     fun b  ->
                                       FStar_TypeChecker_Env.push_binders env
                                         [b])
                                  FStar_Reflection_Embeddings.e_env
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Reflection_Embeddings.e_env
                                  (fun env  ->
                                     fun b  ->
                                       FStar_TypeChecker_Env.push_binders env
                                         [b])
                                  FStar_Reflection_NBEEmbeddings.e_env
                                  FStar_Reflection_NBEEmbeddings.e_binder
                                  FStar_Reflection_NBEEmbeddings.e_env
                                 in
                              let uu____74551 =
                                let uu____74554 =
                                  let uu____74555 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal
                                     in
                                  let uu____74560 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe
                                     in
                                  FStar_Tactics_InterpFuns.mktac1
                                    (Prims.parse_int "0") "set_goals"
                                    FStar_Tactics_Basic.set_goals uu____74555
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Basic.set_goals uu____74560
                                    FStar_TypeChecker_NBETerm.e_unit
                                   in
                                let uu____74571 =
                                  let uu____74574 =
                                    let uu____74575 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Tactics_Embedding.e_goal
                                       in
                                    let uu____74580 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Tactics_Embedding.e_goal_nbe
                                       in
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "set_smt_goals"
                                      FStar_Tactics_Basic.set_smt_goals
                                      uu____74575
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.set_smt_goals
                                      uu____74580
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____74591 =
                                    let uu____74594 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        (Prims.parse_int "0") "trivial"
                                        FStar_Tactics_Basic.trivial
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.trivial
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____74597 =
                                      let uu____74600 =
                                        let uu____74601 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____74606 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____74613 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        let uu____74618 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        FStar_Tactics_InterpFuns.mktac2
                                          (Prims.parse_int "1") "catch"
                                          (fun uu____74640  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____74601 uu____74606
                                          (fun uu____74642  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____74613 uu____74618
                                         in
                                      let uu____74643 =
                                        let uu____74646 =
                                          let uu____74647 =
                                            e_tactic_thunk
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____74652 =
                                            FStar_Syntax_Embeddings.e_either
                                              FStar_Tactics_Embedding.e_exn
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____74659 =
                                            e_tactic_nbe_thunk
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          let uu____74664 =
                                            FStar_TypeChecker_NBETerm.e_either
                                              FStar_Tactics_Embedding.e_exn_nbe
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          FStar_Tactics_InterpFuns.mktac2
                                            (Prims.parse_int "1") "recover"
                                            (fun uu____74686  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_Syntax_Embeddings.e_any
                                            uu____74647 uu____74652
                                            (fun uu____74688  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_TypeChecker_NBETerm.e_any
                                            uu____74659 uu____74664
                                           in
                                        let uu____74689 =
                                          let uu____74692 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              (Prims.parse_int "0") "intro"
                                              FStar_Tactics_Basic.intro
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Tactics_Basic.intro
                                              FStar_TypeChecker_NBETerm.e_unit
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                             in
                                          let uu____74695 =
                                            let uu____74698 =
                                              let uu____74699 =
                                                FStar_Syntax_Embeddings.e_tuple2
                                                  FStar_Reflection_Embeddings.e_binder
                                                  FStar_Reflection_Embeddings.e_binder
                                                 in
                                              let uu____74706 =
                                                FStar_TypeChecker_NBETerm.e_tuple2
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                 in
                                              FStar_Tactics_InterpFuns.mktac1
                                                (Prims.parse_int "0")
                                                "intro_rec"
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_Syntax_Embeddings.e_unit
                                                uu____74699
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_TypeChecker_NBETerm.e_unit
                                                uu____74706
                                               in
                                            let uu____74723 =
                                              let uu____74726 =
                                                let uu____74727 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step
                                                   in
                                                let uu____74732 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step
                                                   in
                                                FStar_Tactics_InterpFuns.mktac1
                                                  (Prims.parse_int "0")
                                                  "norm"
                                                  FStar_Tactics_Basic.norm
                                                  uu____74727
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.norm
                                                  uu____74732
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                 in
                                              let uu____74743 =
                                                let uu____74746 =
                                                  let uu____74747 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step
                                                     in
                                                  let uu____74752 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step
                                                     in
                                                  FStar_Tactics_InterpFuns.mktac3
                                                    (Prims.parse_int "0")
                                                    "norm_term_env"
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_Embeddings.e_env
                                                    uu____74747
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    uu____74752
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                   in
                                                let uu____74763 =
                                                  let uu____74766 =
                                                    let uu____74767 =
                                                      FStar_Syntax_Embeddings.e_list
                                                        FStar_Syntax_Embeddings.e_norm_step
                                                       in
                                                    let uu____74772 =
                                                      FStar_TypeChecker_NBETerm.e_list
                                                        FStar_TypeChecker_NBETerm.e_norm_step
                                                       in
                                                    FStar_Tactics_InterpFuns.mktac2
                                                      (Prims.parse_int "0")
                                                      "norm_binder_type"
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____74767
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Syntax_Embeddings.e_unit
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____74772
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                      FStar_TypeChecker_NBETerm.e_unit
                                                     in
                                                  let uu____74783 =
                                                    let uu____74786 =
                                                      FStar_Tactics_InterpFuns.mktac2
                                                        (Prims.parse_int "0")
                                                        "rename_to"
                                                        FStar_Tactics_Basic.rename_to
                                                        FStar_Reflection_Embeddings.e_binder
                                                        FStar_Syntax_Embeddings.e_string
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_Basic.rename_to
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                        FStar_TypeChecker_NBETerm.e_string
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                       in
                                                    let uu____74791 =
                                                      let uu____74794 =
                                                        FStar_Tactics_InterpFuns.mktac1
                                                          (Prims.parse_int "0")
                                                          "binder_retype"
                                                          FStar_Tactics_Basic.binder_retype
                                                          FStar_Reflection_Embeddings.e_binder
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_Basic.binder_retype
                                                          FStar_Reflection_NBEEmbeddings.e_binder
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                         in
                                                      let uu____74797 =
                                                        let uu____74800 =
                                                          FStar_Tactics_InterpFuns.mktac1
                                                            (Prims.parse_int "0")
                                                            "revert"
                                                            FStar_Tactics_Basic.revert
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Tactics_Basic.revert
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                           in
                                                        let uu____74803 =
                                                          let uu____74806 =
                                                            FStar_Tactics_InterpFuns.mktac1
                                                              (Prims.parse_int "0")
                                                              "clear_top"
                                                              FStar_Tactics_Basic.clear_top
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.clear_top
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                             in
                                                          let uu____74809 =
                                                            let uu____74812 =
                                                              FStar_Tactics_InterpFuns.mktac1
                                                                (Prims.parse_int "0")
                                                                "clear"
                                                                FStar_Tactics_Basic.clear
                                                                FStar_Reflection_Embeddings.e_binder
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_Basic.clear
                                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            let uu____74815 =
                                                              let uu____74818
                                                                =
                                                                FStar_Tactics_InterpFuns.mktac1
                                                                  (Prims.parse_int "0")
                                                                  "rewrite"
                                                                  FStar_Tactics_Basic.rewrite
                                                                  FStar_Reflection_Embeddings.e_binder
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Tactics_Basic.rewrite
                                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                                  FStar_TypeChecker_NBETerm.e_unit
                                                                 in
                                                              let uu____74821
                                                                =
                                                                let uu____74824
                                                                  =
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
                                                                let uu____74827
                                                                  =
                                                                  let uu____74830
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "t_exact"
                                                                    FStar_Tactics_Basic.t_exact
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.t_exact
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                  let uu____74837
                                                                    =
                                                                    let uu____74840
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "t_apply"
                                                                    FStar_Tactics_Basic.t_apply
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.t_apply
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____74845
                                                                    =
                                                                    let uu____74848
                                                                    =
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
                                                                    let uu____74851
                                                                    =
                                                                    let uu____74854
                                                                    =
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
                                                                    let uu____74859
                                                                    =
                                                                    let uu____74862
                                                                    =
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
                                                                    let uu____74865
                                                                    =
                                                                    let uu____74868
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
                                                                    let uu____74871
                                                                    =
                                                                    let uu____74874
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____74879
                                                                     ->
                                                                    fun
                                                                    uu____74880
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____74884
                                                                    =
                                                                    let uu____74887
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
                                                                    let uu____74892
                                                                    =
                                                                    let uu____74895
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
                                                                    let uu____74900
                                                                    =
                                                                    let uu____74903
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
                                                                    let uu____74908
                                                                    =
                                                                    let uu____74911
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "debugging"
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____74916
                                                                    =
                                                                    let uu____74919
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
                                                                    let uu____74924
                                                                    =
                                                                    let uu____74927
                                                                    =
                                                                    let uu____74928
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____74933
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "t_pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____74928
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____74933
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____74944
                                                                    =
                                                                    let uu____74947
                                                                    =
                                                                    let uu____74948
                                                                    =
                                                                    let uu____74961
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____74961
                                                                     in
                                                                    let uu____74975
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____74980
                                                                    =
                                                                    let uu____74993
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____74993
                                                                     in
                                                                    let uu____75007
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____74948
                                                                    uu____74975
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____74980
                                                                    uu____75007
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____75038
                                                                    =
                                                                    let uu____75041
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
                                                                    let uu____75044
                                                                    =
                                                                    let uu____75047
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
                                                                    let uu____75050
                                                                    =
                                                                    let uu____75053
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "tadmit_t"
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____75056
                                                                    =
                                                                    let uu____75059
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "join"
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____75062
                                                                    =
                                                                    let uu____75065
                                                                    =
                                                                    let uu____75066
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____75073
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
                                                                    uu____75066
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____75073
                                                                     in
                                                                    let uu____75090
                                                                    =
                                                                    let uu____75093
                                                                    =
                                                                    let uu____75094
                                                                    =
                                                                    let uu____75103
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____75103
                                                                     in
                                                                    let uu____75114
                                                                    =
                                                                    let uu____75123
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____75123
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____75094
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____75114
                                                                     in
                                                                    let uu____75148
                                                                    =
                                                                    let uu____75151
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
                                                                    let uu____75154
                                                                    =
                                                                    let uu____75157
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
                                                                    let uu____75160
                                                                    =
                                                                    let uu____75163
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
                                                                    let uu____75166
                                                                    =
                                                                    let uu____75169
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
                                                                    let uu____75172
                                                                    =
                                                                    let uu____75175
                                                                    =
                                                                    let uu____75176
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____75181
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____75176
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____75181
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____75192
                                                                    =
                                                                    let uu____75195
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
                                                                    let uu____75200
                                                                    =
                                                                    let uu____75203
                                                                    =
                                                                    let uu____75204
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____75211
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____75204
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____75211
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____75232
                                                                    =
                                                                    let uu____75235
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
                                                                    let uu____75240
                                                                    =
                                                                    let uu____75243
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
                                                                    let uu____75246
                                                                    =
                                                                    let uu____75249
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
                                                                    let uu____75252
                                                                    =
                                                                    let uu____75255
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
                                                                    let uu____75258
                                                                    =
                                                                    let uu____75261
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
                                                                    let uu____75266
                                                                    =
                                                                    let uu____75269
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____75276
                                                                     ->
                                                                    fun
                                                                    uu____75277
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____75280
                                                                    =
                                                                    let uu____75283
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "1")
                                                                    "lset"
                                                                    FStar_Tactics_Basic.lset
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    (fun
                                                                    uu____75291
                                                                     ->
                                                                    fun
                                                                    uu____75292
                                                                     ->
                                                                    fun
                                                                    uu____75293
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____75283]
                                                                     in
                                                                    uu____75269
                                                                    ::
                                                                    uu____75280
                                                                     in
                                                                    uu____75261
                                                                    ::
                                                                    uu____75266
                                                                     in
                                                                    uu____75255
                                                                    ::
                                                                    uu____75258
                                                                     in
                                                                    uu____75249
                                                                    ::
                                                                    uu____75252
                                                                     in
                                                                    uu____75243
                                                                    ::
                                                                    uu____75246
                                                                     in
                                                                    uu____75235
                                                                    ::
                                                                    uu____75240
                                                                     in
                                                                    uu____75203
                                                                    ::
                                                                    uu____75232
                                                                     in
                                                                    uu____75195
                                                                    ::
                                                                    uu____75200
                                                                     in
                                                                    uu____75175
                                                                    ::
                                                                    uu____75192
                                                                     in
                                                                    uu____75169
                                                                    ::
                                                                    uu____75172
                                                                     in
                                                                    uu____75163
                                                                    ::
                                                                    uu____75166
                                                                     in
                                                                    uu____75157
                                                                    ::
                                                                    uu____75160
                                                                     in
                                                                    uu____75151
                                                                    ::
                                                                    uu____75154
                                                                     in
                                                                    uu____75093
                                                                    ::
                                                                    uu____75148
                                                                     in
                                                                    uu____75065
                                                                    ::
                                                                    uu____75090
                                                                     in
                                                                    uu____75059
                                                                    ::
                                                                    uu____75062
                                                                     in
                                                                    uu____75053
                                                                    ::
                                                                    uu____75056
                                                                     in
                                                                    uu____75047
                                                                    ::
                                                                    uu____75050
                                                                     in
                                                                    uu____75041
                                                                    ::
                                                                    uu____75044
                                                                     in
                                                                    uu____74947
                                                                    ::
                                                                    uu____75038
                                                                     in
                                                                    uu____74927
                                                                    ::
                                                                    uu____74944
                                                                     in
                                                                    uu____74919
                                                                    ::
                                                                    uu____74924
                                                                     in
                                                                    uu____74911
                                                                    ::
                                                                    uu____74916
                                                                     in
                                                                    uu____74903
                                                                    ::
                                                                    uu____74908
                                                                     in
                                                                    uu____74895
                                                                    ::
                                                                    uu____74900
                                                                     in
                                                                    uu____74887
                                                                    ::
                                                                    uu____74892
                                                                     in
                                                                    uu____74874
                                                                    ::
                                                                    uu____74884
                                                                     in
                                                                    uu____74868
                                                                    ::
                                                                    uu____74871
                                                                     in
                                                                    uu____74862
                                                                    ::
                                                                    uu____74865
                                                                     in
                                                                    uu____74854
                                                                    ::
                                                                    uu____74859
                                                                     in
                                                                    uu____74848
                                                                    ::
                                                                    uu____74851
                                                                     in
                                                                    uu____74840
                                                                    ::
                                                                    uu____74845
                                                                     in
                                                                  uu____74830
                                                                    ::
                                                                    uu____74837
                                                                   in
                                                                uu____74824
                                                                  ::
                                                                  uu____74827
                                                                 in
                                                              uu____74818 ::
                                                                uu____74821
                                                               in
                                                            uu____74812 ::
                                                              uu____74815
                                                             in
                                                          uu____74806 ::
                                                            uu____74809
                                                           in
                                                        uu____74800 ::
                                                          uu____74803
                                                         in
                                                      uu____74794 ::
                                                        uu____74797
                                                       in
                                                    uu____74786 ::
                                                      uu____74791
                                                     in
                                                  uu____74766 :: uu____74783
                                                   in
                                                uu____74746 :: uu____74763
                                                 in
                                              uu____74726 :: uu____74743  in
                                            uu____74698 :: uu____74723  in
                                          uu____74692 :: uu____74695  in
                                        uu____74646 :: uu____74689  in
                                      uu____74600 :: uu____74643  in
                                    uu____74594 :: uu____74597  in
                                  uu____74574 :: uu____74591  in
                                uu____74554 :: uu____74571  in
                              uu____74492 :: uu____74551  in
                            uu____74484 :: uu____74489  in
                          uu____74476 :: uu____74481  in
                        uu____74468 :: uu____74473  in
                      uu____74462 :: uu____74465  in
                    uu____74456 :: uu____74459  in
                  uu____74450 :: uu____74453  in
                uu____74430 :: uu____74447  in
              uu____74410 :: uu____74427  in
            uu____74404 :: uu____74407  in
          uu____74398 :: uu____74401  in
        uu____74392 :: uu____74395  in
      uu____74386 :: uu____74389  in
    let uu____75296 =
      let uu____75299 = FStar_Tactics_InterpFuns.native_tactics_steps ()  in
      FStar_List.append FStar_Reflection_Interpreter.reflection_primops
        uu____75299
       in
    FStar_List.append uu____74383 uu____75296

and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            'Aa -> 'Ar FStar_Tactics_Basic.tac
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          fun x  ->
            let rng = FStar_Range.dummyRange  in
            let x_tm = FStar_Tactics_InterpFuns.embed ea rng x ncb  in
            let app =
              let uu____75320 =
                let uu____75325 =
                  let uu____75326 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____75326]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____75325  in
              uu____75320 FStar_Pervasives_Native.None rng  in
            unembed_tactic_0 er app ncb

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
             let embedded_tac_b1 = FStar_Syntax_Util.mk_reify embedded_tac_b
                in
             let tm =
               let uu____75383 =
                 let uu____75388 =
                   let uu____75389 =
                     let uu____75398 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____75398  in
                   [uu____75389]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____75388
                  in
               uu____75383 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____75443 = FStar_Options.tactics_nbe ()  in
               if uu____75443
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____75466 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____75466)
             else ();
             (let result =
                let uu____75472 = primitive_steps ()  in
                norm_f uu____75472 steps
                  proof_state.FStar_Tactics_Types.main_context tm
                 in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____75477 = FStar_Syntax_Print.term_to_string result
                    in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____75477)
              else ();
              (let res =
                 let uu____75487 = FStar_Tactics_Embedding.e_result eb  in
                 FStar_Tactics_InterpFuns.unembed uu____75487 result ncb  in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b,ps)) ->
                   let uu____75502 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____75502
                     (fun uu____75506  -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (e,ps)) ->
                   let uu____75511 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____75511
                     (fun uu____75515  -> FStar_Tactics_Basic.traise e)
               | FStar_Pervasives_Native.None  ->
                   let uu____75518 =
                     let uu____75524 =
                       let uu____75526 =
                         FStar_Syntax_Print.term_to_string result  in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____75526
                        in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____75524)  in
                   FStar_Errors.raise_error uu____75518
                     (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.nbe_cbs ->
          FStar_TypeChecker_NBETerm.t -> 'Aa -> 'Ar FStar_Tactics_Basic.tac
  =
  fun ea  ->
    fun er  ->
      fun cb  ->
        fun f  ->
          fun x  ->
            let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x  in
            let app =
              let uu____75543 =
                let uu____75544 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____75544]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____75543  in
            unembed_tactic_nbe_0 er cb app

and unembed_tactic_nbe_0 :
  'Ab .
    'Ab FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.nbe_cbs ->
        FStar_TypeChecker_NBETerm.t -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun cb  ->
      fun embedded_tac_b  ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state  ->
             let result =
               let uu____75570 =
                 let uu____75571 =
                   let uu____75576 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____75576  in
                 [uu____75571]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b
                 uu____75570
                in
             let res =
               let uu____75590 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____75590 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____75603 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____75603
                   (fun uu____75607  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____75612 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____75612
                   (fun uu____75616  -> FStar_Tactics_Basic.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____75619 =
                   let uu____75625 =
                     let uu____75627 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____75627
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____75625)  in
                 FStar_Errors.raise_error uu____75619
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
                 let uu____75660 =
                   let uu____75665 =
                     let uu____75666 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____75666]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____75665  in
                 uu____75660 FStar_Pervasives_Native.None rng  in
               unembed_tactic_0 er app ncb)

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
      let em uu____75747 uu____75748 uu____75749 uu____75750 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n1 =
        let uu____75821 = unembed_tactic_1_alt ea er t0 n1  in
        match uu____75821 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____75863 = f x  in
                  FStar_Tactics_Basic.run uu____75863))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____75879 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____75879

let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____75919 =
               let uu____75921 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____75923 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____75921 uu____75923 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____75919, rng)) is
         in
      FStar_Errors.add_errors errs; FStar_Errors.stop_if_err ()
  
let (run_tactic_on_typ :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.typ ->
            (FStar_Tactics_Types.goal Prims.list * FStar_Syntax_Syntax.term))
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun typ  ->
            (let uu____75967 = FStar_ST.op_Bang tacdbg  in
             if uu____75967
             then
               let uu____75991 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____75991
             else ());
            (let uu____75996 = FStar_TypeChecker_TcTerm.tc_tactic env tactic
                in
             match uu____75996 with
             | (uu____76009,uu____76010,g) ->
                 ((let uu____76013 = FStar_ST.op_Bang tacdbg  in
                   if uu____76013 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_1 FStar_Syntax_Embeddings.e_unit
                       FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb
                      in
                   let uu____76049 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____76049 with
                   | (env1,uu____76063) ->
                       let env2 =
                         let uu___806_76069 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___806_76069.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___806_76069.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___806_76069.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___806_76069.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___806_76069.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___806_76069.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___806_76069.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___806_76069.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___806_76069.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___806_76069.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___806_76069.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___806_76069.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___806_76069.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___806_76069.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___806_76069.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___806_76069.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___806_76069.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___806_76069.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___806_76069.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___806_76069.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___806_76069.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___806_76069.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___806_76069.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___806_76069.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___806_76069.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___806_76069.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___806_76069.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___806_76069.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___806_76069.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___806_76069.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___806_76069.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___806_76069.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___806_76069.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___806_76069.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___806_76069.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___806_76069.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___806_76069.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___806_76069.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___806_76069.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___806_76069.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___806_76069.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___806_76069.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___809_76072 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___809_76072.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___809_76072.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___809_76072.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___809_76072.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___809_76072.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___809_76072.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___809_76072.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___809_76072.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___809_76072.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___809_76072.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___809_76072.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___809_76072.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___809_76072.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___809_76072.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___809_76072.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___809_76072.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___809_76072.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___809_76072.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___809_76072.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___809_76072.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___809_76072.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___809_76072.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___809_76072.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___809_76072.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___809_76072.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___809_76072.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___809_76072.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___809_76072.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___809_76072.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___809_76072.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___809_76072.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___809_76072.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___809_76072.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___809_76072.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___809_76072.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___809_76072.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___809_76072.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___809_76072.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___809_76072.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___809_76072.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___809_76072.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___809_76072.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___812_76075 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___812_76075.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___812_76075.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___812_76075.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___812_76075.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___812_76075.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___812_76075.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___812_76075.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___812_76075.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___812_76075.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___812_76075.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___812_76075.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___812_76075.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___812_76075.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___812_76075.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___812_76075.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___812_76075.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___812_76075.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___812_76075.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___812_76075.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___812_76075.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___812_76075.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___812_76075.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___812_76075.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___812_76075.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___812_76075.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___812_76075.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___812_76075.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___812_76075.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___812_76075.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___812_76075.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___812_76075.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___812_76075.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___812_76075.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___812_76075.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___812_76075.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___812_76075.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___812_76075.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___812_76075.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___812_76075.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___812_76075.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___812_76075.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___812_76075.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____76078 = FStar_Range.use_range rng_goal  in
                         let uu____76079 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____76078 uu____76079  in
                       let uu____76080 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____76080 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____76118 = FStar_ST.op_Bang tacdbg  in
                              if uu____76118
                              then
                                let uu____76142 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____76142
                              else ());
                             (let uu____76147 =
                                FStar_Util.record_time
                                  (fun uu____76159  ->
                                     let uu____76160 = tau ()  in
                                     FStar_Tactics_Basic.run_safe uu____76160
                                       ps)
                                 in
                              match uu____76147 with
                              | (res,ms) ->
                                  ((let uu____76178 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____76178
                                    then FStar_Util.print_string "}\n"
                                    else ());
                                   (let uu____76206 =
                                      (FStar_ST.op_Bang tacdbg) ||
                                        (FStar_Options.tactics_info ())
                                       in
                                    if uu____76206
                                    then
                                      let uu____76230 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____76232 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____76234 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "Tactic %s ran in %s ms (%s)\n"
                                        uu____76230 uu____76232 uu____76234
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____76245,ps1) ->
                                        ((let uu____76248 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____76248
                                          then
                                            let uu____76272 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____76272
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____76282 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____76282
                                              then
                                                let uu____76285 =
                                                  let uu____76287 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____76288 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt_force
                                                    uu____76287 uu____76288
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____76285
                                                 then ()
                                                 else
                                                   (let uu____76292 =
                                                      let uu____76294 =
                                                        let uu____76296 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____76296
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____76294
                                                       in
                                                    failwith uu____76292))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____76301 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____76301
                                          then
                                            let uu____76325 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____76325
                                          else ());
                                         (let g1 =
                                            let uu___843_76333 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___843_76333.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___843_76333.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___843_76333.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____76336 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____76336
                                           then
                                             let uu____76360 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits)
                                                in
                                             let uu____76362 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____76360 uu____76362
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____76371 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____76371
                                            then
                                              let uu____76395 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits)
                                                 in
                                              let uu____76397 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____76395 uu____76397
                                            else ());
                                           report_implicits rng_goal
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____76406 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____76406
                                            then
                                              let uu____76430 =
                                                let uu____76431 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc
                                                   in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____76431 ps1
                                                 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____76430
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (e,ps1) ->
                                        ((let uu____76440 =
                                            let uu____76441 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____76441 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____76440
                                            "at the time of failure");
                                         (let texn_to_string e1 =
                                            match e1 with
                                            | FStar_Tactics_Types.TacticFailure
                                                s -> s
                                            | FStar_Tactics_Types.EExn t ->
                                                let uu____76454 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                Prims.op_Hat
                                                  "uncaught exception: "
                                                  uu____76454
                                            | e2 -> FStar_Exn.raise e2  in
                                          let uu____76459 =
                                            let uu____76465 =
                                              let uu____76467 =
                                                texn_to_string e  in
                                              FStar_Util.format1
                                                "user tactic failed: %s"
                                                uu____76467
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____76465)
                                             in
                                          FStar_Errors.raise_error
                                            uu____76459
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pos  -> true | uu____76486 -> false
  
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neg  -> true | uu____76497 -> false
  
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____76508 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____76567 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____76612 -> false
  
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____76671 -> false
  
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____76715 . 'Auu____76715 -> 'Auu____76715 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____76745 = FStar_Syntax_Util.head_and_args t  in
        match uu____76745 with
        | (hd1,args) ->
            let uu____76788 =
              let uu____76803 =
                let uu____76804 = FStar_Syntax_Util.un_uinst hd1  in
                uu____76804.FStar_Syntax_Syntax.n  in
              (uu____76803, args)  in
            (match uu____76788 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____76819))::(tactic,FStar_Pervasives_Native.None
                                                                  )::
                (assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____76883 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____76883 with
                       | (gs,uu____76891) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____76898 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____76898 with
                       | (gs,uu____76906) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____76949 =
                        let uu____76956 =
                          let uu____76959 =
                            let uu____76960 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____76960
                             in
                          [uu____76959]  in
                        (FStar_Syntax_Util.t_true, uu____76956)  in
                      Simplified uu____76949
                  | Both  ->
                      let uu____76971 =
                        let uu____76980 =
                          let uu____76983 =
                            let uu____76984 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____76984
                             in
                          [uu____76983]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____76980)
                         in
                      Dual uu____76971
                  | Neg  -> Simplified (assertion, []))
             | uu____76997 -> Unchanged t)
  
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___613_77089  ->
      match uu___613_77089 with
      | Unchanged t -> let uu____77095 = f t  in Unchanged uu____77095
      | Simplified (t,gs) ->
          let uu____77102 = let uu____77109 = f t  in (uu____77109, gs)  in
          Simplified uu____77102
      | Dual (tn,tp,gs) ->
          let uu____77119 =
            let uu____77128 = f tn  in
            let uu____77129 = f tp  in (uu____77128, uu____77129, gs)  in
          Dual uu____77119
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____77193 = f t1 t2  in Unchanged uu____77193
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____77205 = let uu____77212 = f t1 t2  in (uu____77212, gs)
               in
            Simplified uu____77205
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____77226 = let uu____77233 = f t1 t2  in (uu____77233, gs)
               in
            Simplified uu____77226
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____77252 =
              let uu____77259 = f t1 t2  in
              (uu____77259, (FStar_List.append gs1 gs2))  in
            Simplified uu____77252
        | uu____77262 ->
            let uu____77271 = explode x  in
            (match uu____77271 with
             | (n1,p1,gs1) ->
                 let uu____77289 = explode y  in
                 (match uu____77289 with
                  | (n2,p2,gs2) ->
                      let uu____77307 =
                        let uu____77316 = f n1 n2  in
                        let uu____77317 = f p1 p2  in
                        (uu____77316, uu____77317,
                          (FStar_List.append gs1 gs2))
                         in
                      Dual uu____77307))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____77390 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____77390
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____77439  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____77482 =
              let uu____77483 = FStar_Syntax_Subst.compress t  in
              uu____77483.FStar_Syntax_Syntax.n  in
            match uu____77482 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____77495 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____77495 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____77521 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____77521 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____77541;
                   FStar_Syntax_Syntax.vars = uu____77542;_},(p,uu____77544)::
                 (q,uu____77546)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____77604 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____77604 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____77618 = FStar_Syntax_Util.mk_imp l r  in
                       uu____77618.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____77622;
                   FStar_Syntax_Syntax.vars = uu____77623;_},(p,uu____77625)::
                 (q,uu____77627)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let xq =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q
                   in
                let r1 =
                  let uu____77685 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____77685 p  in
                let r2 =
                  let uu____77687 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____77687 q  in
                (match (r1, r2) with
                 | (Unchanged uu____77694,Unchanged uu____77695) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____77713 = FStar_Syntax_Util.mk_iff l r
                               in
                            uu____77713.FStar_Syntax_Syntax.n) r1 r2
                 | uu____77716 ->
                     let uu____77725 = explode r1  in
                     (match uu____77725 with
                      | (pn,pp,gs1) ->
                          let uu____77743 = explode r2  in
                          (match uu____77743 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____77764 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____77767 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____77764
                                   uu____77767
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____77831  ->
                       fun r  ->
                         match uu____77831 with
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
                let uu____77983 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____77983 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____78023  ->
                            match uu____78023 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____78045 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___1106_78077 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1106_78077.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1106_78077.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____78045 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____78105 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____78105.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____78151 = traverse f pol e t1  in
                let uu____78156 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____78156 uu____78151
            | FStar_Syntax_Syntax.Tm_match (sc,brs) ->
                let uu____78231 = traverse f pol e sc  in
                let uu____78236 =
                  let uu____78255 =
                    FStar_List.map
                      (fun br  ->
                         let uu____78272 = FStar_Syntax_Subst.open_branch br
                            in
                         match uu____78272 with
                         | (pat,w,exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs
                                in
                             let r = traverse f pol e1 exp  in
                             let uu____78299 =
                               comb1
                                 (fun exp1  ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1))
                                in
                             uu____78299 r) brs
                     in
                  comb_list uu____78255  in
                comb2
                  (fun sc1  ->
                     fun brs1  -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____78231 uu____78236
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___1138_78385 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___1138_78385.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1138_78385.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____78392 =
                f pol e
                  (let uu___1144_78396 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___1144_78396.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1144_78396.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____78392
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___1151_78406 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___1151_78406.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1151_78406.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____78407 = explode rp  in
              (match uu____78407 with
               | (uu____78416,p',gs') ->
                   Dual
                     ((let uu___1158_78426 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___1158_78426.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___1158_78426.FStar_Syntax_Syntax.vars)
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
      (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
        FStar_Options.optionstate) Prims.list)
  =
  fun env  ->
    fun goal  ->
      (let uu____78471 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____78471);
      (let uu____78496 = FStar_ST.op_Bang tacdbg  in
       if uu____78496
       then
         let uu____78520 =
           let uu____78522 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____78522
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____78525 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____78520
           uu____78525
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____78560 =
         let uu____78569 = traverse by_tactic_interp Pos env goal  in
         match uu____78569 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____78593 -> failwith "no"  in
       match uu____78560 with
       | (t',gs) ->
           ((let uu____78622 = FStar_ST.op_Bang tacdbg  in
             if uu____78622
             then
               let uu____78646 =
                 let uu____78648 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____78648
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____78651 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____78646 uu____78651
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____78706  ->
                    fun g  ->
                      match uu____78706 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____78755 =
                              let uu____78758 =
                                FStar_Tactics_Types.goal_env g  in
                              let uu____78759 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____78758 uu____78759  in
                            match uu____78755 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____78760 =
                                  let uu____78766 =
                                    let uu____78768 =
                                      let uu____78770 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____78770
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____78768
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____78766)
                                   in
                                FStar_Errors.raise_error uu____78760
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____78775 = FStar_ST.op_Bang tacdbg  in
                            if uu____78775
                            then
                              let uu____78799 = FStar_Util.string_of_int n1
                                 in
                              let uu____78801 =
                                let uu____78803 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____78803
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____78799 uu____78801
                            else ());
                           (let label1 =
                              let uu____78809 =
                                let uu____78811 =
                                  FStar_Tactics_Types.get_label g  in
                                uu____78811 = ""  in
                              if uu____78809
                              then
                                let uu____78817 = FStar_Util.string_of_int n1
                                   in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____78817
                              else
                                (let uu____78822 =
                                   let uu____78824 =
                                     FStar_Util.string_of_int n1  in
                                   let uu____78826 =
                                     let uu____78828 =
                                       let uu____78830 =
                                         FStar_Tactics_Types.get_label g  in
                                       Prims.op_Hat uu____78830 ")"  in
                                     Prims.op_Hat " (" uu____78828  in
                                   Prims.op_Hat uu____78824 uu____78826  in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____78822)
                               in
                            let gt' =
                              FStar_TypeChecker_Util.label label1
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____78836 =
                              let uu____78845 =
                                let uu____78852 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____78852, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____78845 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____78836)))) s
                 gs
                in
             let uu____78869 = s1  in
             match uu____78869 with
             | (uu____78891,gs1) ->
                 let uu____78911 =
                   let uu____78918 = FStar_Options.peek ()  in
                   (env, t', uu____78918)  in
                 uu____78911 :: gs1)))
  
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
          let uu____78942 =
            let uu____78947 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____78948 =
              let uu____78949 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____78949]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____78947 uu____78948  in
          uu____78942 FStar_Pervasives_Native.None
            typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____78979 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____78979);
           (let uu____79003 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____79003 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____79024 =
                        let uu____79027 = FStar_Tactics_Types.goal_env g  in
                        let uu____79028 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____79027 uu____79028  in
                      match uu____79024 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____79031 = FStar_ST.op_Bang tacdbg  in
                            if uu____79031
                            then
                              let uu____79055 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____79055
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____79070 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____79070 guard))
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
        ((let uu____79092 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____79092);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____79117 =
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos tau env typ
             in
          match uu____79117 with
          | (gs,w) ->
              ((let uu____79133 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____79138 =
                         let uu____79140 =
                           let uu____79143 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____79144 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____79143 uu____79144  in
                         FStar_Option.isSome uu____79140  in
                       Prims.op_Negation uu____79138) gs
                   in
                if uu____79133
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
                (let uu____79152 = FStar_ST.op_Bang tacdbg  in
                 if uu____79152
                 then
                   let uu____79176 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____79176
                 else ());
                (let uu____79181 =
                   let uu____79186 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____79186 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____79181 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  
let (postprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun tau  ->
      fun typ  ->
        fun tm  ->
          if env.FStar_TypeChecker_Env.nosynth
          then tm
          else
            ((let uu____79231 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")
                 in
              FStar_ST.op_Colon_Equals tacdbg uu____79231);
             (let uu____79255 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None
                 in
              match uu____79255 with
              | (uvtm,uu____79274,g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ  in
                  let goal =
                    let uu____79292 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm
                       in
                    FStar_Syntax_Util.mk_squash u uu____79292  in
                  let uu____79293 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal
                     in
                  (match uu____79293 with
                   | (gs,w) ->
                       (FStar_List.iter
                          (fun g  ->
                             let uu____79314 =
                               let uu____79317 =
                                 FStar_Tactics_Types.goal_env g  in
                               let uu____79318 =
                                 FStar_Tactics_Types.goal_type g  in
                               getprop uu____79317 uu____79318  in
                             match uu____79314 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____79321 = FStar_ST.op_Bang tacdbg
                                      in
                                   if uu____79321
                                   then
                                     let uu____79345 =
                                       FStar_Syntax_Print.term_to_string vc
                                        in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____79345
                                   else ());
                                  (let guard =
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         (FStar_TypeChecker_Common.NonTrivial
                                            vc);
                                       FStar_TypeChecker_Env.deferred = [];
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         ([], []);
                                       FStar_TypeChecker_Env.implicits = []
                                     }  in
                                   let uu____79360 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____79360 guard))
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Errors.raise_error
                                   (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                                     "postprocessing left open goals")
                                   typ.FStar_Syntax_Syntax.pos) gs;
                        (let g_imp1 =
                           FStar_TypeChecker_Rel.resolve_implicits_tac env
                             g_imp
                            in
                         report_implicits tm.FStar_Syntax_Syntax.pos
                           g_imp1.FStar_TypeChecker_Env.implicits;
                         uvtm)))))
  