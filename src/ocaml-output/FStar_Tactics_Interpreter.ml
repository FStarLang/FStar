open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let mktot1' :
  'Auu____30 'Auu____31 'Auu____32 'Auu____33 .
    Prims.int ->
      Prims.string ->
        ('Auu____30 -> 'Auu____31) ->
          'Auu____30 FStar_Syntax_Embeddings.embedding ->
            'Auu____31 FStar_Syntax_Embeddings.embedding ->
              ('Auu____32 -> 'Auu____33) ->
                'Auu____32 FStar_TypeChecker_NBETerm.embedding ->
                  'Auu____33 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___9_104 =
                    FStar_Tactics_InterpFuns.mktot1 uarity nm f ea er nf ena
                      enr
                     in
                  let uu____105 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____105;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___9_104.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___9_104.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___9_104.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___9_104.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___9_104.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___9_104.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___9_104.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot1'_psc :
  'Auu____132 'Auu____133 'Auu____134 'Auu____135 .
    Prims.int ->
      Prims.string ->
        (FStar_TypeChecker_Cfg.psc -> 'Auu____132 -> 'Auu____133) ->
          'Auu____132 FStar_Syntax_Embeddings.embedding ->
            'Auu____133 FStar_Syntax_Embeddings.embedding ->
              (FStar_TypeChecker_Cfg.psc -> 'Auu____134 -> 'Auu____135) ->
                'Auu____134 FStar_TypeChecker_NBETerm.embedding ->
                  'Auu____135 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___19_216 =
                    FStar_Tactics_InterpFuns.mktot1_psc uarity nm f ea er nf
                      ena enr
                     in
                  let uu____217 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____217;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___19_216.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___19_216.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___19_216.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___19_216.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___19_216.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___19_216.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___19_216.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot2' :
  'Auu____252 'Auu____253 'Auu____254 'Auu____255 'Auu____256 'Auu____257 .
    Prims.int ->
      Prims.string ->
        ('Auu____252 -> 'Auu____253 -> 'Auu____254) ->
          'Auu____252 FStar_Syntax_Embeddings.embedding ->
            'Auu____253 FStar_Syntax_Embeddings.embedding ->
              'Auu____254 FStar_Syntax_Embeddings.embedding ->
                ('Auu____255 -> 'Auu____256 -> 'Auu____257) ->
                  'Auu____255 FStar_TypeChecker_NBETerm.embedding ->
                    'Auu____256 FStar_TypeChecker_NBETerm.embedding ->
                      'Auu____257 FStar_TypeChecker_NBETerm.embedding ->
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
                      let uu___31_356 =
                        FStar_Tactics_InterpFuns.mktot2 uarity nm f ea eb er
                          nf ena enb enr
                         in
                      let uu____357 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm)
                         in
                      {
                        FStar_TypeChecker_Cfg.name = uu____357;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___31_356.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___31_356.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___31_356.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___31_356.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___31_356.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___31_356.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___31_356.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
  
let rec e_tactic_thunk :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Monad.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____589 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____596  ->
         fun uu____597  ->
           fun uu____598  ->
             fun uu____599  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____613 =
               let uu____616 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____616 ()  in
             FStar_Pervasives_Native.Some uu____613) uu____589

and e_tactic_nbe_thunk :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Monad.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____628 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____634  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____643 =
             let uu____646 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____646 ()  in
           FStar_Pervasives_Native.Some uu____643)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____628

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Monad.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____661 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____671  ->
           fun uu____672  ->
             fun uu____673  ->
               fun uu____674  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____690 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____690) uu____661

and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Monad.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____708 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____717  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____728 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____728)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____708

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____740  ->
    let uu____743 =
      let uu____746 =
        mktot1'_psc Prims.int_zero "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____749 =
        let uu____752 =
          mktot2' Prims.int_zero "set_proofstate_range"
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Syntax_Embeddings.e_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_TypeChecker_NBETerm.e_range
            FStar_Tactics_Embedding.e_proofstate_nbe
           in
        let uu____755 =
          let uu____758 =
            mktot1' Prims.int_zero "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe
             in
          let uu____761 =
            let uu____764 =
              mktot1' Prims.int_zero "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____767 =
              let uu____770 =
                let uu____771 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal
                   in
                let uu____776 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe
                   in
                mktot1' Prims.int_zero "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____771
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____776
                 in
              let uu____787 =
                let uu____790 =
                  let uu____791 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____796 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mktot1' Prims.int_zero "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____791
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____796
                   in
                let uu____807 =
                  let uu____810 =
                    mktot1' Prims.int_zero "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env
                     in
                  let uu____813 =
                    let uu____816 =
                      mktot1' Prims.int_zero "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term
                       in
                    let uu____819 =
                      let uu____822 =
                        mktot1' Prims.int_zero "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____825 =
                        let uu____828 =
                          mktot1' Prims.int_zero "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool
                           in
                        let uu____833 =
                          let uu____836 =
                            mktot1' Prims.int_zero "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string
                             in
                          let uu____841 =
                            let uu____844 =
                              mktot2' Prims.int_zero "set_label"
                                FStar_Tactics_Types.set_label
                                FStar_Syntax_Embeddings.e_string
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Types.set_label
                                FStar_TypeChecker_NBETerm.e_string
                                FStar_Tactics_Embedding.e_goal_nbe
                                FStar_Tactics_Embedding.e_goal_nbe
                               in
                            let uu____849 =
                              let uu____852 =
                                FStar_Tactics_InterpFuns.mktot2
                                  Prims.int_zero "push_binder"
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
                              let uu____911 =
                                let uu____914 =
                                  let uu____915 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal
                                     in
                                  let uu____920 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe
                                     in
                                  FStar_Tactics_InterpFuns.mktac1
                                    Prims.int_zero "set_goals"
                                    FStar_Tactics_Monad.set_goals uu____915
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Monad.set_goals uu____920
                                    FStar_TypeChecker_NBETerm.e_unit
                                   in
                                let uu____931 =
                                  let uu____934 =
                                    let uu____935 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Tactics_Embedding.e_goal
                                       in
                                    let uu____940 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Tactics_Embedding.e_goal_nbe
                                       in
                                    FStar_Tactics_InterpFuns.mktac1
                                      Prims.int_zero "set_smt_goals"
                                      FStar_Tactics_Monad.set_smt_goals
                                      uu____935
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Monad.set_smt_goals
                                      uu____940
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____951 =
                                    let uu____954 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        Prims.int_zero "trivial"
                                        FStar_Tactics_Basic.trivial
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.trivial
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____957 =
                                      let uu____960 =
                                        let uu____961 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____966 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____973 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        let uu____978 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        FStar_Tactics_InterpFuns.mktac2
                                          Prims.int_one "catch"
                                          (fun uu____1000  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____961 uu____966
                                          (fun uu____1002  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____973 uu____978
                                         in
                                      let uu____1003 =
                                        let uu____1006 =
                                          let uu____1007 =
                                            e_tactic_thunk
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____1012 =
                                            FStar_Syntax_Embeddings.e_either
                                              FStar_Tactics_Embedding.e_exn
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____1019 =
                                            e_tactic_nbe_thunk
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          let uu____1024 =
                                            FStar_TypeChecker_NBETerm.e_either
                                              FStar_Tactics_Embedding.e_exn_nbe
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          FStar_Tactics_InterpFuns.mktac2
                                            Prims.int_one "recover"
                                            (fun uu____1046  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_Syntax_Embeddings.e_any
                                            uu____1007 uu____1012
                                            (fun uu____1048  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_TypeChecker_NBETerm.e_any
                                            uu____1019 uu____1024
                                           in
                                        let uu____1049 =
                                          let uu____1052 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              Prims.int_zero "intro"
                                              FStar_Tactics_Basic.intro
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Tactics_Basic.intro
                                              FStar_TypeChecker_NBETerm.e_unit
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                             in
                                          let uu____1055 =
                                            let uu____1058 =
                                              let uu____1059 =
                                                FStar_Syntax_Embeddings.e_tuple2
                                                  FStar_Reflection_Embeddings.e_binder
                                                  FStar_Reflection_Embeddings.e_binder
                                                 in
                                              let uu____1066 =
                                                FStar_TypeChecker_NBETerm.e_tuple2
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                 in
                                              FStar_Tactics_InterpFuns.mktac1
                                                Prims.int_zero "intro_rec"
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_Syntax_Embeddings.e_unit
                                                uu____1059
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_TypeChecker_NBETerm.e_unit
                                                uu____1066
                                               in
                                            let uu____1083 =
                                              let uu____1086 =
                                                let uu____1087 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step
                                                   in
                                                let uu____1092 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step
                                                   in
                                                FStar_Tactics_InterpFuns.mktac1
                                                  Prims.int_zero "norm"
                                                  FStar_Tactics_Basic.norm
                                                  uu____1087
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.norm
                                                  uu____1092
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                 in
                                              let uu____1103 =
                                                let uu____1106 =
                                                  let uu____1107 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step
                                                     in
                                                  let uu____1112 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step
                                                     in
                                                  FStar_Tactics_InterpFuns.mktac3
                                                    Prims.int_zero
                                                    "norm_term_env"
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_Embeddings.e_env
                                                    uu____1107
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    uu____1112
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                   in
                                                let uu____1123 =
                                                  let uu____1126 =
                                                    let uu____1127 =
                                                      FStar_Syntax_Embeddings.e_list
                                                        FStar_Syntax_Embeddings.e_norm_step
                                                       in
                                                    let uu____1132 =
                                                      FStar_TypeChecker_NBETerm.e_list
                                                        FStar_TypeChecker_NBETerm.e_norm_step
                                                       in
                                                    FStar_Tactics_InterpFuns.mktac2
                                                      Prims.int_zero
                                                      "norm_binder_type"
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____1127
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Syntax_Embeddings.e_unit
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____1132
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                      FStar_TypeChecker_NBETerm.e_unit
                                                     in
                                                  let uu____1143 =
                                                    let uu____1146 =
                                                      FStar_Tactics_InterpFuns.mktac2
                                                        Prims.int_zero
                                                        "rename_to"
                                                        FStar_Tactics_Basic.rename_to
                                                        FStar_Reflection_Embeddings.e_binder
                                                        FStar_Syntax_Embeddings.e_string
                                                        FStar_Reflection_Embeddings.e_binder
                                                        FStar_Tactics_Basic.rename_to
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                        FStar_TypeChecker_NBETerm.e_string
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                       in
                                                    let uu____1151 =
                                                      let uu____1154 =
                                                        FStar_Tactics_InterpFuns.mktac1
                                                          Prims.int_zero
                                                          "binder_retype"
                                                          FStar_Tactics_Basic.binder_retype
                                                          FStar_Reflection_Embeddings.e_binder
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_Basic.binder_retype
                                                          FStar_Reflection_NBEEmbeddings.e_binder
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                         in
                                                      let uu____1157 =
                                                        let uu____1160 =
                                                          FStar_Tactics_InterpFuns.mktac1
                                                            Prims.int_zero
                                                            "revert"
                                                            FStar_Tactics_Basic.revert
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Tactics_Basic.revert
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                           in
                                                        let uu____1163 =
                                                          let uu____1166 =
                                                            FStar_Tactics_InterpFuns.mktac1
                                                              Prims.int_zero
                                                              "clear_top"
                                                              FStar_Tactics_Basic.clear_top
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.clear_top
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                             in
                                                          let uu____1169 =
                                                            let uu____1172 =
                                                              FStar_Tactics_InterpFuns.mktac1
                                                                Prims.int_zero
                                                                "clear"
                                                                FStar_Tactics_Basic.clear
                                                                FStar_Reflection_Embeddings.e_binder
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_Basic.clear
                                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            let uu____1175 =
                                                              let uu____1178
                                                                =
                                                                FStar_Tactics_InterpFuns.mktac1
                                                                  Prims.int_zero
                                                                  "rewrite"
                                                                  FStar_Tactics_Basic.rewrite
                                                                  FStar_Reflection_Embeddings.e_binder
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Tactics_Basic.rewrite
                                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                                  FStar_TypeChecker_NBETerm.e_unit
                                                                 in
                                                              let uu____1181
                                                                =
                                                                let uu____1184
                                                                  =
                                                                  FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "refine_intro"
                                                                    FStar_Tactics_Basic.refine_intro
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.refine_intro
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                   in
                                                                let uu____1187
                                                                  =
                                                                  let uu____1190
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
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
                                                                  let uu____1197
                                                                    =
                                                                    let uu____1200
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "t_apply"
                                                                    FStar_Tactics_Basic.t_apply
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.t_apply
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1207
                                                                    =
                                                                    let uu____1210
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "apply_lemma"
                                                                    FStar_Tactics_Basic.apply_lemma
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.apply_lemma
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1213
                                                                    =
                                                                    let uu____1216
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "set_options"
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1221
                                                                    =
                                                                    let uu____1224
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "tcc"
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_comp
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_comp
                                                                     in
                                                                    let uu____1227
                                                                    =
                                                                    let uu____1230
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "tc"
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1233
                                                                    =
                                                                    let uu____1236
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "unshelve"
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1239
                                                                    =
                                                                    let uu____1242
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1247
                                                                     ->
                                                                    fun
                                                                    uu____1248
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1252
                                                                    =
                                                                    let uu____1255
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "prune"
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1260
                                                                    =
                                                                    let uu____1263
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "addns"
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1268
                                                                    =
                                                                    let uu____1271
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "print"
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1276
                                                                    =
                                                                    let uu____1279
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "debugging"
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1284
                                                                    =
                                                                    let uu____1287
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "dump"
                                                                    FStar_Tactics_Basic.dump
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dump
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1292
                                                                    =
                                                                    let uu____1295
                                                                    =
                                                                    let uu____1296
                                                                    =
                                                                    let uu____1309
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1309
                                                                     in
                                                                    let uu____1323
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1328
                                                                    =
                                                                    let uu____1341
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1341
                                                                     in
                                                                    let uu____1355
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1296
                                                                    uu____1323
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1328
                                                                    uu____1355
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1386
                                                                    =
                                                                    let uu____1389
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1392
                                                                    =
                                                                    let uu____1395
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1398
                                                                    =
                                                                    let uu____1401
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "tadmit_t"
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1404
                                                                    =
                                                                    let uu____1407
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "join"
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1410
                                                                    =
                                                                    let uu____1413
                                                                    =
                                                                    let uu____1414
                                                                    =
                                                                    let uu____1423
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1423
                                                                     in
                                                                    let uu____1434
                                                                    =
                                                                    let uu____1443
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1443
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1414
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1434
                                                                     in
                                                                    let uu____1468
                                                                    =
                                                                    let uu____1471
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                     in
                                                                    let uu____1474
                                                                    =
                                                                    let uu____1477
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                     in
                                                                    let uu____1480
                                                                    =
                                                                    let uu____1483
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1486
                                                                    =
                                                                    let uu____1489
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    let uu____1492
                                                                    =
                                                                    let uu____1495
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "curms"
                                                                    FStar_Tactics_Basic.curms
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.curms
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    let uu____1498
                                                                    =
                                                                    let uu____1501
                                                                    =
                                                                    let uu____1502
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1507
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1502
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1507
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1518
                                                                    =
                                                                    let uu____1521
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
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
                                                                    let uu____1526
                                                                    =
                                                                    let uu____1529
                                                                    =
                                                                    let uu____1530
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1537
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1530
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1537
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1558
                                                                    =
                                                                    let uu____1561
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
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
                                                                    let uu____1566
                                                                    =
                                                                    let uu____1569
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1572
                                                                    =
                                                                    let uu____1575
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                     in
                                                                    let uu____1578
                                                                    =
                                                                    let uu____1581
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1584
                                                                    =
                                                                    let uu____1587
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "lax_on"
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1592
                                                                    =
                                                                    let uu____1595
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1602
                                                                     ->
                                                                    fun
                                                                    uu____1603
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1606
                                                                    =
                                                                    let uu____1609
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_one
                                                                    "lset"
                                                                    FStar_Tactics_Basic.lset
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    (fun
                                                                    uu____1617
                                                                     ->
                                                                    fun
                                                                    uu____1618
                                                                     ->
                                                                    fun
                                                                    uu____1619
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____1609]
                                                                     in
                                                                    uu____1595
                                                                    ::
                                                                    uu____1606
                                                                     in
                                                                    uu____1587
                                                                    ::
                                                                    uu____1592
                                                                     in
                                                                    uu____1581
                                                                    ::
                                                                    uu____1584
                                                                     in
                                                                    uu____1575
                                                                    ::
                                                                    uu____1578
                                                                     in
                                                                    uu____1569
                                                                    ::
                                                                    uu____1572
                                                                     in
                                                                    uu____1561
                                                                    ::
                                                                    uu____1566
                                                                     in
                                                                    uu____1529
                                                                    ::
                                                                    uu____1558
                                                                     in
                                                                    uu____1521
                                                                    ::
                                                                    uu____1526
                                                                     in
                                                                    uu____1501
                                                                    ::
                                                                    uu____1518
                                                                     in
                                                                    uu____1495
                                                                    ::
                                                                    uu____1498
                                                                     in
                                                                    uu____1489
                                                                    ::
                                                                    uu____1492
                                                                     in
                                                                    uu____1483
                                                                    ::
                                                                    uu____1486
                                                                     in
                                                                    uu____1477
                                                                    ::
                                                                    uu____1480
                                                                     in
                                                                    uu____1471
                                                                    ::
                                                                    uu____1474
                                                                     in
                                                                    uu____1413
                                                                    ::
                                                                    uu____1468
                                                                     in
                                                                    uu____1407
                                                                    ::
                                                                    uu____1410
                                                                     in
                                                                    uu____1401
                                                                    ::
                                                                    uu____1404
                                                                     in
                                                                    uu____1395
                                                                    ::
                                                                    uu____1398
                                                                     in
                                                                    uu____1389
                                                                    ::
                                                                    uu____1392
                                                                     in
                                                                    uu____1295
                                                                    ::
                                                                    uu____1386
                                                                     in
                                                                    uu____1287
                                                                    ::
                                                                    uu____1292
                                                                     in
                                                                    uu____1279
                                                                    ::
                                                                    uu____1284
                                                                     in
                                                                    uu____1271
                                                                    ::
                                                                    uu____1276
                                                                     in
                                                                    uu____1263
                                                                    ::
                                                                    uu____1268
                                                                     in
                                                                    uu____1255
                                                                    ::
                                                                    uu____1260
                                                                     in
                                                                    uu____1242
                                                                    ::
                                                                    uu____1252
                                                                     in
                                                                    uu____1236
                                                                    ::
                                                                    uu____1239
                                                                     in
                                                                    uu____1230
                                                                    ::
                                                                    uu____1233
                                                                     in
                                                                    uu____1224
                                                                    ::
                                                                    uu____1227
                                                                     in
                                                                    uu____1216
                                                                    ::
                                                                    uu____1221
                                                                     in
                                                                    uu____1210
                                                                    ::
                                                                    uu____1213
                                                                     in
                                                                    uu____1200
                                                                    ::
                                                                    uu____1207
                                                                     in
                                                                  uu____1190
                                                                    ::
                                                                    uu____1197
                                                                   in
                                                                uu____1184 ::
                                                                  uu____1187
                                                                 in
                                                              uu____1178 ::
                                                                uu____1181
                                                               in
                                                            uu____1172 ::
                                                              uu____1175
                                                             in
                                                          uu____1166 ::
                                                            uu____1169
                                                           in
                                                        uu____1160 ::
                                                          uu____1163
                                                         in
                                                      uu____1154 ::
                                                        uu____1157
                                                       in
                                                    uu____1146 :: uu____1151
                                                     in
                                                  uu____1126 :: uu____1143
                                                   in
                                                uu____1106 :: uu____1123  in
                                              uu____1086 :: uu____1103  in
                                            uu____1058 :: uu____1083  in
                                          uu____1052 :: uu____1055  in
                                        uu____1006 :: uu____1049  in
                                      uu____960 :: uu____1003  in
                                    uu____954 :: uu____957  in
                                  uu____934 :: uu____951  in
                                uu____914 :: uu____931  in
                              uu____852 :: uu____911  in
                            uu____844 :: uu____849  in
                          uu____836 :: uu____841  in
                        uu____828 :: uu____833  in
                      uu____822 :: uu____825  in
                    uu____816 :: uu____819  in
                  uu____810 :: uu____813  in
                uu____790 :: uu____807  in
              uu____770 :: uu____787  in
            uu____764 :: uu____767  in
          uu____758 :: uu____761  in
        uu____752 :: uu____755  in
      uu____746 :: uu____749  in
    let uu____1622 = FStar_Tactics_InterpFuns.native_tactics_steps ()  in
    FStar_List.append uu____743 uu____1622

and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            'Aa -> 'Ar FStar_Tactics_Monad.tac
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          fun x  ->
            let rng = FStar_Range.dummyRange  in
            let x_tm = FStar_Tactics_InterpFuns.embed ea rng x ncb  in
            let app =
              let uu____1640 =
                let uu____1645 =
                  let uu____1646 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____1646]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____1645  in
              uu____1640 FStar_Pervasives_Native.None rng  in
            unembed_tactic_0 er app ncb

and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb -> 'Ab FStar_Tactics_Monad.tac
  =
  fun eb  ->
    fun embedded_tac_b  ->
      fun ncb  ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun proof_state  ->
             let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
             let embedded_tac_b1 = FStar_Syntax_Util.mk_reify embedded_tac_b
                in
             let tm =
               let uu____1696 =
                 let uu____1701 =
                   let uu____1702 =
                     let uu____1711 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1711  in
                   [uu____1702]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1701  in
               uu____1696 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1752 = FStar_Options.tactics_nbe ()  in
               if uu____1752
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             let result =
               let uu____1774 = primitive_steps ()  in
               norm_f uu____1774 steps
                 proof_state.FStar_Tactics_Types.main_context tm
                in
             let res =
               let uu____1782 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Tactics_InterpFuns.unembed uu____1782 result ncb  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1795 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____1795
                   (fun uu____1799  -> FStar_Tactics_Monad.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1804 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____1804
                   (fun uu____1808  -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____1811 =
                   let uu____1817 =
                     let uu____1819 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1819
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1817)  in
                 FStar_Errors.raise_error uu____1811
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

and unembed_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.nbe_cbs ->
          FStar_TypeChecker_NBETerm.t -> 'Aa -> 'Ar FStar_Tactics_Monad.tac
  =
  fun ea  ->
    fun er  ->
      fun cb  ->
        fun f  ->
          fun x  ->
            let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x  in
            let app =
              let uu____1836 =
                let uu____1837 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____1837]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1836  in
            unembed_tactic_nbe_0 er cb app

and unembed_tactic_nbe_0 :
  'Ab .
    'Ab FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.nbe_cbs ->
        FStar_TypeChecker_NBETerm.t -> 'Ab FStar_Tactics_Monad.tac
  =
  fun eb  ->
    fun cb  ->
      fun embedded_tac_b  ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun proof_state  ->
             let result =
               let uu____1863 =
                 let uu____1864 =
                   let uu____1869 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1869  in
                 [uu____1864]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1863
                in
             let res =
               let uu____1883 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1883 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1896 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____1896
                   (fun uu____1900  -> FStar_Tactics_Monad.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1905 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____1905
                   (fun uu____1909  -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____1912 =
                   let uu____1918 =
                     let uu____1920 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1920
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1918)  in
                 FStar_Errors.raise_error uu____1912
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

let unembed_tactic_1_alt :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            ('Aa -> 'Ar FStar_Tactics_Monad.tac)
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
                 let uu____1993 =
                   let uu____1998 =
                     let uu____1999 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____1999]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1998  in
                 uu____1993 FStar_Pervasives_Native.None rng  in
               unembed_tactic_0 er app ncb)
  
let e_tactic_1_alt :
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
      let em uu____2089 uu____2090 uu____2091 uu____2092 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n1 =
        let uu____2141 = unembed_tactic_1_alt ea er t0 n1  in
        match uu____2141 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____2181 = f x  in FStar_Tactics_Monad.run uu____2181))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____2197 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____2197
  
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____2237 =
               let uu____2239 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____2241 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2239 uu____2241
                 imp.FStar_TypeChecker_Common.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2237, rng)) is
         in
      FStar_Errors.add_errors errs; FStar_Errors.stop_if_err ()
  
let run_tactic_on_ps :
  'a 'b .
    FStar_Range.range ->
      FStar_Range.range ->
        'a FStar_Syntax_Embeddings.embedding ->
          'a ->
            'b FStar_Syntax_Embeddings.embedding ->
              FStar_Syntax_Syntax.term ->
                FStar_TypeChecker_Env.env ->
                  FStar_Tactics_Types.proofstate ->
                    (FStar_Tactics_Types.goal Prims.list * 'b)
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun e_arg  ->
        fun arg  ->
          fun e_res  ->
            fun tactic  ->
              fun env  ->
                fun ps  ->
                  (let uu____2324 = FStar_ST.op_Bang tacdbg  in
                   if uu____2324
                   then
                     let uu____2348 =
                       FStar_Syntax_Print.term_to_string tactic  in
                     FStar_Util.print1 "Typechecking tactic: (%s) {\n"
                       uu____2348
                   else ());
                  (let uu____2353 =
                     let uu____2360 = FStar_Syntax_Embeddings.type_of e_arg
                        in
                     let uu____2361 = FStar_Syntax_Embeddings.type_of e_res
                        in
                     FStar_TypeChecker_TcTerm.tc_tactic uu____2360 uu____2361
                       env tactic
                      in
                   match uu____2353 with
                   | (uu____2368,uu____2369,g) ->
                       ((let uu____2372 = FStar_ST.op_Bang tacdbg  in
                         if uu____2372
                         then FStar_Util.print_string "}\n"
                         else ());
                        FStar_TypeChecker_Rel.force_trivial_guard env g;
                        FStar_Errors.stop_if_err ();
                        (let tau =
                           unembed_tactic_1 e_arg e_res tactic
                             FStar_Syntax_Embeddings.id_norm_cb
                            in
                         FStar_ST.op_Colon_Equals
                           FStar_Reflection_Basic.env_hook
                           (FStar_Pervasives_Native.Some env);
                         (let uu____2432 =
                            FStar_Util.record_time
                              (fun uu____2444  ->
                                 let uu____2445 = tau arg  in
                                 FStar_Tactics_Monad.run_safe uu____2445 ps)
                             in
                          match uu____2432 with
                          | (res,ms) ->
                              ((let uu____2463 = FStar_ST.op_Bang tacdbg  in
                                if uu____2463
                                then FStar_Util.print_string "}\n"
                                else ());
                               (let uu____2491 =
                                  (FStar_ST.op_Bang tacdbg) ||
                                    (FStar_Options.tactics_info ())
                                   in
                                if uu____2491
                                then
                                  let uu____2515 =
                                    FStar_Syntax_Print.term_to_string tactic
                                     in
                                  let uu____2517 =
                                    FStar_Util.string_of_int ms  in
                                  let uu____2519 =
                                    FStar_Syntax_Print.lid_to_string
                                      env.FStar_TypeChecker_Env.curmodule
                                     in
                                  FStar_Util.print3
                                    "Tactic %s ran in %s ms (%s)\n"
                                    uu____2515 uu____2517 uu____2519
                                else ());
                               (match res with
                                | FStar_Tactics_Result.Success (ret1,ps1) ->
                                    (FStar_List.iter
                                       (fun g1  ->
                                          let uu____2537 =
                                            FStar_Tactics_Basic.is_irrelevant
                                              g1
                                             in
                                          if uu____2537
                                          then
                                            let uu____2540 =
                                              let uu____2542 =
                                                FStar_Tactics_Types.goal_env
                                                  g1
                                                 in
                                              let uu____2543 =
                                                FStar_Tactics_Types.goal_witness
                                                  g1
                                                 in
                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                uu____2542 uu____2543
                                                FStar_Syntax_Util.exp_unit
                                               in
                                            (if uu____2540
                                             then ()
                                             else
                                               (let uu____2547 =
                                                  let uu____2549 =
                                                    let uu____2551 =
                                                      FStar_Tactics_Types.goal_witness
                                                        g1
                                                       in
                                                    FStar_Syntax_Print.term_to_string
                                                      uu____2551
                                                     in
                                                  FStar_Util.format1
                                                    "Irrelevant tactic witness does not unify with (): %s"
                                                    uu____2549
                                                   in
                                                failwith uu____2547))
                                          else ())
                                       (FStar_List.append
                                          ps1.FStar_Tactics_Types.goals
                                          ps1.FStar_Tactics_Types.smt_goals);
                                     (let uu____2556 =
                                        FStar_ST.op_Bang tacdbg  in
                                      if uu____2556
                                      then
                                        let uu____2580 =
                                          FStar_Common.string_of_list
                                            (fun imp  ->
                                               FStar_Syntax_Print.ctx_uvar_to_string
                                                 imp.FStar_TypeChecker_Common.imp_uvar)
                                            ps1.FStar_Tactics_Types.all_implicits
                                           in
                                        FStar_Util.print1
                                          "About to check tactic implicits: %s\n"
                                          uu____2580
                                      else ());
                                     (let g1 =
                                        let uu___221_2588 =
                                          FStar_TypeChecker_Env.trivial_guard
                                           in
                                        {
                                          FStar_TypeChecker_Common.guard_f =
                                            (uu___221_2588.FStar_TypeChecker_Common.guard_f);
                                          FStar_TypeChecker_Common.deferred =
                                            (uu___221_2588.FStar_TypeChecker_Common.deferred);
                                          FStar_TypeChecker_Common.univ_ineqs
                                            =
                                            (uu___221_2588.FStar_TypeChecker_Common.univ_ineqs);
                                          FStar_TypeChecker_Common.implicits
                                            =
                                            (ps1.FStar_Tactics_Types.all_implicits)
                                        }  in
                                      let g2 =
                                        FStar_TypeChecker_Rel.solve_deferred_constraints
                                          env g1
                                         in
                                      (let uu____2591 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____2591
                                       then
                                         let uu____2615 =
                                           FStar_Util.string_of_int
                                             (FStar_List.length
                                                ps1.FStar_Tactics_Types.all_implicits)
                                            in
                                         let uu____2617 =
                                           FStar_Common.string_of_list
                                             (fun imp  ->
                                                FStar_Syntax_Print.ctx_uvar_to_string
                                                  imp.FStar_TypeChecker_Common.imp_uvar)
                                             ps1.FStar_Tactics_Types.all_implicits
                                            in
                                         FStar_Util.print2
                                           "Checked %s implicits (1): %s\n"
                                           uu____2615 uu____2617
                                       else ());
                                      (let g3 =
                                         FStar_TypeChecker_Rel.resolve_implicits_tac
                                           env g2
                                          in
                                       (let uu____2626 =
                                          FStar_ST.op_Bang tacdbg  in
                                        if uu____2626
                                        then
                                          let uu____2650 =
                                            FStar_Util.string_of_int
                                              (FStar_List.length
                                                 ps1.FStar_Tactics_Types.all_implicits)
                                             in
                                          let uu____2652 =
                                            FStar_Common.string_of_list
                                              (fun imp  ->
                                                 FStar_Syntax_Print.ctx_uvar_to_string
                                                   imp.FStar_TypeChecker_Common.imp_uvar)
                                              ps1.FStar_Tactics_Types.all_implicits
                                             in
                                          FStar_Util.print2
                                            "Checked %s implicits (2): %s\n"
                                            uu____2650 uu____2652
                                        else ());
                                       report_implicits rng_goal
                                         g3.FStar_TypeChecker_Common.implicits;
                                       (let uu____2661 =
                                          FStar_ST.op_Bang tacdbg  in
                                        if uu____2661
                                        then
                                          let uu____2685 =
                                            let uu____2686 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____2686 ps1
                                             in
                                          FStar_Tactics_Printing.do_dump_proofstate
                                            uu____2685 "at the finish line"
                                        else ());
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         ret1))))
                                | FStar_Tactics_Result.Failed (e,ps1) ->
                                    ((let uu____2695 =
                                        let uu____2696 =
                                          FStar_TypeChecker_Cfg.psc_subst
                                            ps1.FStar_Tactics_Types.psc
                                           in
                                        FStar_Tactics_Types.subst_proof_state
                                          uu____2696 ps1
                                         in
                                      FStar_Tactics_Printing.do_dump_proofstate
                                        uu____2695 "at the time of failure");
                                     (let texn_to_string e1 =
                                        match e1 with
                                        | FStar_Tactics_Types.TacticFailure s
                                            -> s
                                        | FStar_Tactics_Types.EExn t ->
                                            let uu____2709 =
                                              FStar_Syntax_Print.term_to_string
                                                t
                                               in
                                            Prims.op_Hat
                                              "uncaught exception: "
                                              uu____2709
                                        | e2 -> FStar_Exn.raise e2  in
                                      let uu____2714 =
                                        let uu____2720 =
                                          let uu____2722 = texn_to_string e
                                             in
                                          FStar_Util.format1
                                            "user tactic failed: %s"
                                            uu____2722
                                           in
                                        (FStar_Errors.Fatal_UserTacticFailure,
                                          uu____2720)
                                         in
                                      FStar_Errors.raise_error uu____2714
                                        ps1.FStar_Tactics_Types.entry_range))))))))
  
let (run_tactic_on_typ :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term ->
            (FStar_Tactics_Types.goal Prims.list * FStar_Syntax_Syntax.term))
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun typ  ->
            let rng =
              let uu____2771 = FStar_Range.use_range rng_goal  in
              let uu____2772 = FStar_Range.use_range rng_tac  in
              FStar_Range.range_of_rng uu____2771 uu____2772  in
            let uu____2773 =
              FStar_Tactics_Basic.proofstate_of_goal_ty rng env typ  in
            match uu____2773 with
            | (ps,w) ->
                let uu____2786 =
                  run_tactic_on_ps rng_tac rng_goal
                    FStar_Syntax_Embeddings.e_unit ()
                    FStar_Syntax_Embeddings.e_unit tactic env ps
                   in
                (match uu____2786 with | (gs,_res) -> (gs, w))
  
let (run_tactic_on_all_implicits :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_TypeChecker_Env.implicits ->
            FStar_Tactics_Types.goal Prims.list)
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun imps  ->
            let uu____2837 =
              FStar_Tactics_Basic.proofstate_of_all_implicits rng_goal env
                imps
               in
            match uu____2837 with
            | (ps,uu____2845) ->
                let uu____2846 =
                  run_tactic_on_ps rng_tac rng_goal
                    FStar_Syntax_Embeddings.e_unit ()
                    FStar_Syntax_Embeddings.e_unit tactic env ps
                   in
                (match uu____2846 with | (goals,()) -> goals)
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2869 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2880 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2891 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2950 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2994 -> false
  
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3052 -> false
  
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____3095 . 'Auu____3095 -> 'Auu____3095 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3125 = FStar_Syntax_Util.head_and_args t  in
        match uu____3125 with
        | (hd1,args) ->
            let uu____3168 =
              let uu____3183 =
                let uu____3184 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3184.FStar_Syntax_Syntax.n  in
              (uu____3183, args)  in
            (match uu____3168 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(tactic,FStar_Pervasives_Native.None )::(assertion,FStar_Pervasives_Native.None
                                                            )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3246 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3246 with
                       | (gs,uu____3254) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3261 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3261 with
                       | (gs,uu____3269) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3312 =
                        let uu____3319 =
                          let uu____3322 =
                            let uu____3323 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3323
                             in
                          [uu____3322]  in
                        (FStar_Syntax_Util.t_true, uu____3319)  in
                      Simplified uu____3312
                  | Both  ->
                      let uu____3334 =
                        let uu____3343 =
                          let uu____3346 =
                            let uu____3347 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3347
                             in
                          [uu____3346]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3343)  in
                      Dual uu____3334
                  | Neg  -> Simplified (assertion, []))
             | uu____3360 -> Unchanged t)
  
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___0_3452  ->
      match uu___0_3452 with
      | Unchanged t -> let uu____3458 = f t  in Unchanged uu____3458
      | Simplified (t,gs) ->
          let uu____3465 = let uu____3472 = f t  in (uu____3472, gs)  in
          Simplified uu____3465
      | Dual (tn,tp,gs) ->
          let uu____3482 =
            let uu____3491 = f tn  in
            let uu____3492 = f tp  in (uu____3491, uu____3492, gs)  in
          Dual uu____3482
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3556 = f t1 t2  in Unchanged uu____3556
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3568 = let uu____3575 = f t1 t2  in (uu____3575, gs)
               in
            Simplified uu____3568
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3589 = let uu____3596 = f t1 t2  in (uu____3596, gs)
               in
            Simplified uu____3589
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3615 =
              let uu____3622 = f t1 t2  in
              (uu____3622, (FStar_List.append gs1 gs2))  in
            Simplified uu____3615
        | uu____3625 ->
            let uu____3634 = explode x  in
            (match uu____3634 with
             | (n1,p1,gs1) ->
                 let uu____3652 = explode y  in
                 (match uu____3652 with
                  | (n2,p2,gs2) ->
                      let uu____3670 =
                        let uu____3679 = f n1 n2  in
                        let uu____3680 = f p1 p2  in
                        (uu____3679, uu____3680, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3670))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3753 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3753
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3802  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3845 =
              let uu____3846 = FStar_Syntax_Subst.compress t  in
              uu____3846.FStar_Syntax_Syntax.n  in
            match uu____3845 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3858 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3858 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3884 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3884 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3904;
                   FStar_Syntax_Syntax.vars = uu____3905;_},(p,uu____3907)::
                 (q,uu____3909)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3967 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3967 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3981 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3981.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3985;
                   FStar_Syntax_Syntax.vars = uu____3986;_},(p,uu____3988)::
                 (q,uu____3990)::[])
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
                  let uu____4048 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4048 p  in
                let r2 =
                  let uu____4050 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4050 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4057,Unchanged uu____4058) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4076 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4076.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4079 ->
                     let uu____4088 = explode r1  in
                     (match uu____4088 with
                      | (pn,pp,gs1) ->
                          let uu____4106 = explode r2  in
                          (match uu____4106 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4127 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4130 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4127
                                   uu____4130
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4194  ->
                       fun r  ->
                         match uu____4194 with
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
                let uu____4346 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4346 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4386  ->
                            match uu____4386 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4408 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___502_4440 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___502_4440.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___502_4440.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4408 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4468 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4468.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4514 = traverse f pol e t1  in
                let uu____4519 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4519 uu____4514
            | FStar_Syntax_Syntax.Tm_match (sc,brs) ->
                let uu____4594 = traverse f pol e sc  in
                let uu____4599 =
                  let uu____4618 =
                    FStar_List.map
                      (fun br  ->
                         let uu____4635 = FStar_Syntax_Subst.open_branch br
                            in
                         match uu____4635 with
                         | (pat,w,exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs
                                in
                             let r = traverse f pol e1 exp  in
                             let uu____4662 =
                               comb1
                                 (fun exp1  ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1))
                                in
                             uu____4662 r) brs
                     in
                  comb_list uu____4618  in
                comb2
                  (fun sc1  ->
                     fun brs1  -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____4594 uu____4599
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___534_4748 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___534_4748.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___534_4748.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4755 =
                f pol e
                  (let uu___540_4759 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___540_4759.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___540_4759.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4755
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___547_4769 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___547_4769.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___547_4769.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4770 = explode rp  in
              (match uu____4770 with
               | (uu____4779,p',gs') ->
                   Dual
                     ((let uu___554_4789 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___554_4789.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___554_4789.FStar_Syntax_Syntax.vars)
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
      (let uu____4834 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4834);
      (let uu____4859 = FStar_ST.op_Bang tacdbg  in
       if uu____4859
       then
         let uu____4883 =
           let uu____4885 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4885
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4888 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4883
           uu____4888
       else ());
      (let initial = (Prims.int_one, [])  in
       let uu____4923 =
         let uu____4932 = traverse by_tactic_interp Pos env goal  in
         match uu____4932 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4956 -> failwith "no"  in
       match uu____4923 with
       | (t',gs) ->
           ((let uu____4985 = FStar_ST.op_Bang tacdbg  in
             if uu____4985
             then
               let uu____5009 =
                 let uu____5011 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____5011
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____5014 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____5009 uu____5014
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5069  ->
                    fun g  ->
                      match uu____5069 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____5118 =
                              let uu____5121 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____5122 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____5121 uu____5122  in
                            match uu____5118 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5123 =
                                  let uu____5129 =
                                    let uu____5131 =
                                      let uu____5133 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____5133
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5131
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5129)
                                   in
                                FStar_Errors.raise_error uu____5123
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5138 = FStar_ST.op_Bang tacdbg  in
                            if uu____5138
                            then
                              let uu____5162 = FStar_Util.string_of_int n1
                                 in
                              let uu____5164 =
                                let uu____5166 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____5166
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5162 uu____5164
                            else ());
                           (let label1 =
                              let uu____5172 =
                                let uu____5174 =
                                  FStar_Tactics_Types.get_label g  in
                                uu____5174 = ""  in
                              if uu____5172
                              then
                                let uu____5180 = FStar_Util.string_of_int n1
                                   in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____5180
                              else
                                (let uu____5185 =
                                   let uu____5187 =
                                     FStar_Util.string_of_int n1  in
                                   let uu____5189 =
                                     let uu____5191 =
                                       let uu____5193 =
                                         FStar_Tactics_Types.get_label g  in
                                       Prims.op_Hat uu____5193 ")"  in
                                     Prims.op_Hat " (" uu____5191  in
                                   Prims.op_Hat uu____5187 uu____5189  in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____5185)
                               in
                            let gt' =
                              FStar_TypeChecker_Util.label label1
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____5199 =
                              let uu____5208 =
                                let uu____5215 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____5215, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____5208 :: gs1  in
                            ((n1 + Prims.int_one), uu____5199)))) s gs
                in
             let uu____5232 = s1  in
             match uu____5232 with
             | (uu____5254,gs1) ->
                 let gs2 = FStar_List.rev gs1  in
                 let uu____5289 =
                   let uu____5296 = FStar_Options.peek ()  in
                   (env, t', uu____5296)  in
                 uu____5289 :: gs2)))
  
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
          let uu____5320 =
            let uu____5325 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____5326 =
              let uu____5327 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5327]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____5325 uu____5326  in
          uu____5320 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____5355 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5355);
           (let uu____5379 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____5379 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____5400 =
                        let uu____5403 = FStar_Tactics_Types.goal_env g  in
                        let uu____5404 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____5403 uu____5404  in
                      match uu____5400 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____5407 = FStar_ST.op_Bang tacdbg  in
                            if uu____5407
                            then
                              let uu____5431 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____5431
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Common.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Common.deferred = [];
                                FStar_TypeChecker_Common.univ_ineqs =
                                  ([], []);
                                FStar_TypeChecker_Common.implicits = []
                              }  in
                            let uu____5446 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____5446 guard))
                      | FStar_Pervasives_Native.None  ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                              "synthesis left open goals")
                            typ.FStar_Syntax_Syntax.pos) gs;
                 w)))
  
let (solve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.implicits -> unit)
  =
  fun env  ->
    fun tau  ->
      fun imps  ->
        if env.FStar_TypeChecker_Env.nosynth
        then ()
        else
          ((let uu____5469 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5469);
           (let gs =
              let uu____5496 = FStar_TypeChecker_Env.get_range env  in
              run_tactic_on_all_implicits tau.FStar_Syntax_Syntax.pos
                uu____5496 tau env imps
               in
            FStar_All.pipe_right gs
              (FStar_List.iter
                 (fun g  ->
                    let uu____5507 =
                      let uu____5510 = FStar_Tactics_Types.goal_env g  in
                      let uu____5511 = FStar_Tactics_Types.goal_type g  in
                      getprop uu____5510 uu____5511  in
                    match uu____5507 with
                    | FStar_Pervasives_Native.Some vc ->
                        ((let uu____5514 = FStar_ST.op_Bang tacdbg  in
                          if uu____5514
                          then
                            let uu____5538 =
                              FStar_Syntax_Print.term_to_string vc  in
                            FStar_Util.print1 "Synthesis left a goal: %s\n"
                              uu____5538
                          else ());
                         (let guard =
                            {
                              FStar_TypeChecker_Common.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Common.deferred = [];
                              FStar_TypeChecker_Common.univ_ineqs = ([], []);
                              FStar_TypeChecker_Common.implicits = []
                            }  in
                          let uu____5553 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____5553 guard))
                    | FStar_Pervasives_Native.None  ->
                        let uu____5554 = FStar_TypeChecker_Env.get_range env
                           in
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                            "synthesis left open goals") uu____5554))))
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      if env.FStar_TypeChecker_Env.nosynth
      then []
      else
        ((let uu____5576 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____5576);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let ps =
            FStar_Tactics_Basic.proofstate_of_goals
              tau.FStar_Syntax_Syntax.pos env [] []
             in
          let uu____5602 =
            let uu____5611 =
              FStar_Syntax_Embeddings.e_list
                FStar_Reflection_Embeddings.e_sigelt
               in
            run_tactic_on_ps tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos FStar_Syntax_Embeddings.e_unit ()
              uu____5611 tau env ps
             in
          match uu____5602 with
          | (gs,sigelts) ->
              ((let uu____5631 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____5636 =
                         let uu____5638 =
                           let uu____5641 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____5642 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____5641 uu____5642  in
                         FStar_Option.isSome uu____5638  in
                       Prims.op_Negation uu____5636) gs
                   in
                if uu____5631
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                      "splice left open goals") typ.FStar_Syntax_Syntax.pos
                else ());
               (let uu____5649 = FStar_ST.op_Bang tacdbg  in
                if uu____5649
                then
                  let uu____5673 =
                    FStar_Common.string_of_list
                      FStar_Syntax_Print.sigelt_to_string sigelts
                     in
                  FStar_Util.print1 "splice: got decls = %s\n" uu____5673
                else ());
               sigelts)))
  
let (mpreprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun tau  ->
      fun tm  ->
        if env.FStar_TypeChecker_Env.nosynth
        then tm
        else
          ((let uu____5698 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5698);
           (let ps =
              FStar_Tactics_Basic.proofstate_of_goals
                tm.FStar_Syntax_Syntax.pos env [] []
               in
            let uu____5723 =
              run_tactic_on_ps tau.FStar_Syntax_Syntax.pos
                tm.FStar_Syntax_Syntax.pos FStar_Reflection_Embeddings.e_term
                tm FStar_Reflection_Embeddings.e_term tau env ps
               in
            match uu____5723 with | (gs,tm1) -> tm1))
  
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
            ((let uu____5761 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")
                 in
              FStar_ST.op_Colon_Equals tacdbg uu____5761);
             (let uu____5785 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None
                 in
              match uu____5785 with
              | (uvtm,uu____5804,g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ  in
                  let goal =
                    let uu____5822 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm
                       in
                    FStar_Syntax_Util.mk_squash u uu____5822  in
                  let uu____5823 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal
                     in
                  (match uu____5823 with
                   | (gs,w) ->
                       (FStar_List.iter
                          (fun g  ->
                             let uu____5844 =
                               let uu____5847 =
                                 FStar_Tactics_Types.goal_env g  in
                               let uu____5848 =
                                 FStar_Tactics_Types.goal_type g  in
                               getprop uu____5847 uu____5848  in
                             match uu____5844 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____5851 = FStar_ST.op_Bang tacdbg
                                      in
                                   if uu____5851
                                   then
                                     let uu____5875 =
                                       FStar_Syntax_Print.term_to_string vc
                                        in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____5875
                                   else ());
                                  (let guard =
                                     {
                                       FStar_TypeChecker_Common.guard_f =
                                         (FStar_TypeChecker_Common.NonTrivial
                                            vc);
                                       FStar_TypeChecker_Common.deferred = [];
                                       FStar_TypeChecker_Common.univ_ineqs =
                                         ([], []);
                                       FStar_TypeChecker_Common.implicits =
                                         []
                                     }  in
                                   let uu____5890 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____5890 guard))
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
                           g_imp1.FStar_TypeChecker_Common.implicits;
                         uvtm)))))
  