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
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
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
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
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
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
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
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
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
                                    FStar_Tactics_Basic.set_goals uu____915
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Basic.set_goals uu____920
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
                                      FStar_Tactics_Basic.set_smt_goals
                                      uu____935
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.set_smt_goals
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
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_Basic.rename_to
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                        FStar_TypeChecker_NBETerm.e_string
                                                        FStar_TypeChecker_NBETerm.e_unit
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
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1301
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "t_pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1296
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1301
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1312
                                                                    =
                                                                    let uu____1315
                                                                    =
                                                                    let uu____1316
                                                                    =
                                                                    let uu____1329
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1329
                                                                     in
                                                                    let uu____1343
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1348
                                                                    =
                                                                    let uu____1361
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1361
                                                                     in
                                                                    let uu____1375
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1316
                                                                    uu____1343
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1348
                                                                    uu____1375
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1406
                                                                    =
                                                                    let uu____1409
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
                                                                    let uu____1412
                                                                    =
                                                                    let uu____1415
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
                                                                    let uu____1418
                                                                    =
                                                                    let uu____1421
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
                                                                    let uu____1424
                                                                    =
                                                                    let uu____1427
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
                                                                    let uu____1430
                                                                    =
                                                                    let uu____1433
                                                                    =
                                                                    let uu____1434
                                                                    =
                                                                    let uu____1443
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1443
                                                                     in
                                                                    let uu____1454
                                                                    =
                                                                    let uu____1463
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1463
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1434
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1454
                                                                     in
                                                                    let uu____1488
                                                                    =
                                                                    let uu____1491
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
                                                                    let uu____1494
                                                                    =
                                                                    let uu____1497
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
                                                                    let uu____1500
                                                                    =
                                                                    let uu____1503
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
                                                                    let uu____1506
                                                                    =
                                                                    let uu____1509
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
                                                                    let uu____1512
                                                                    =
                                                                    let uu____1515
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
                                                                    let uu____1518
                                                                    =
                                                                    let uu____1521
                                                                    =
                                                                    let uu____1522
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1527
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1522
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1527
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1538
                                                                    =
                                                                    let uu____1541
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
                                                                    let uu____1546
                                                                    =
                                                                    let uu____1549
                                                                    =
                                                                    let uu____1550
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1557
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1550
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1557
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1578
                                                                    =
                                                                    let uu____1581
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
                                                                    let uu____1586
                                                                    =
                                                                    let uu____1589
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
                                                                    let uu____1592
                                                                    =
                                                                    let uu____1595
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
                                                                    let uu____1598
                                                                    =
                                                                    let uu____1601
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
                                                                    let uu____1604
                                                                    =
                                                                    let uu____1607
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
                                                                    let uu____1612
                                                                    =
                                                                    let uu____1615
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1622
                                                                     ->
                                                                    fun
                                                                    uu____1623
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1626
                                                                    =
                                                                    let uu____1629
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
                                                                    uu____1637
                                                                     ->
                                                                    fun
                                                                    uu____1638
                                                                     ->
                                                                    fun
                                                                    uu____1639
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____1629]
                                                                     in
                                                                    uu____1615
                                                                    ::
                                                                    uu____1626
                                                                     in
                                                                    uu____1607
                                                                    ::
                                                                    uu____1612
                                                                     in
                                                                    uu____1601
                                                                    ::
                                                                    uu____1604
                                                                     in
                                                                    uu____1595
                                                                    ::
                                                                    uu____1598
                                                                     in
                                                                    uu____1589
                                                                    ::
                                                                    uu____1592
                                                                     in
                                                                    uu____1581
                                                                    ::
                                                                    uu____1586
                                                                     in
                                                                    uu____1549
                                                                    ::
                                                                    uu____1578
                                                                     in
                                                                    uu____1541
                                                                    ::
                                                                    uu____1546
                                                                     in
                                                                    uu____1521
                                                                    ::
                                                                    uu____1538
                                                                     in
                                                                    uu____1515
                                                                    ::
                                                                    uu____1518
                                                                     in
                                                                    uu____1509
                                                                    ::
                                                                    uu____1512
                                                                     in
                                                                    uu____1503
                                                                    ::
                                                                    uu____1506
                                                                     in
                                                                    uu____1497
                                                                    ::
                                                                    uu____1500
                                                                     in
                                                                    uu____1491
                                                                    ::
                                                                    uu____1494
                                                                     in
                                                                    uu____1433
                                                                    ::
                                                                    uu____1488
                                                                     in
                                                                    uu____1427
                                                                    ::
                                                                    uu____1430
                                                                     in
                                                                    uu____1421
                                                                    ::
                                                                    uu____1424
                                                                     in
                                                                    uu____1415
                                                                    ::
                                                                    uu____1418
                                                                     in
                                                                    uu____1409
                                                                    ::
                                                                    uu____1412
                                                                     in
                                                                    uu____1315
                                                                    ::
                                                                    uu____1406
                                                                     in
                                                                    uu____1295
                                                                    ::
                                                                    uu____1312
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
    let uu____1642 = FStar_Tactics_InterpFuns.native_tactics_steps ()  in
    FStar_List.append uu____743 uu____1642

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
              let uu____1660 =
                let uu____1665 =
                  let uu____1666 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____1666]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____1665  in
              uu____1660 FStar_Pervasives_Native.None rng  in
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
               let uu____1716 =
                 let uu____1721 =
                   let uu____1722 =
                     let uu____1731 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1731  in
                   [uu____1722]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1721  in
               uu____1716 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1772 = FStar_Options.tactics_nbe ()  in
               if uu____1772
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             let result =
               let uu____1794 = primitive_steps ()  in
               norm_f uu____1794 steps
                 proof_state.FStar_Tactics_Types.main_context tm
                in
             let res =
               let uu____1802 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Tactics_InterpFuns.unembed uu____1802 result ncb  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1815 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1815
                   (fun uu____1819  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1824 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1824
                   (fun uu____1828  -> FStar_Tactics_Basic.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____1831 =
                   let uu____1837 =
                     let uu____1839 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1839
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1837)  in
                 FStar_Errors.raise_error uu____1831
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

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
              let uu____1856 =
                let uu____1857 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____1857]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1856  in
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
               let uu____1883 =
                 let uu____1884 =
                   let uu____1889 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1889  in
                 [uu____1884]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1883
                in
             let res =
               let uu____1903 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1903 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1916 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1916
                   (fun uu____1920  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1925 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1925
                   (fun uu____1929  -> FStar_Tactics_Basic.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____1932 =
                   let uu____1938 =
                     let uu____1940 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1940
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1938)  in
                 FStar_Errors.raise_error uu____1932
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

let unembed_tactic_1_alt :
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
                 let uu____2013 =
                   let uu____2018 =
                     let uu____2019 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____2019]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____2018  in
                 uu____2013 FStar_Pervasives_Native.None rng  in
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
      let em uu____2109 uu____2110 uu____2111 uu____2112 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n1 =
        let uu____2161 = unembed_tactic_1_alt ea er t0 n1  in
        match uu____2161 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____2201 = f x  in FStar_Tactics_Basic.run uu____2201))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____2217 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____2217
  
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____2257 =
               let uu____2259 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____2261 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2259 uu____2261
                 imp.FStar_TypeChecker_Common.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2257, rng)) is
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
                  (let uu____2344 = FStar_ST.op_Bang tacdbg  in
                   if uu____2344
                   then
                     let uu____2368 =
                       FStar_Syntax_Print.term_to_string tactic  in
                     FStar_Util.print1 "Typechecking tactic: (%s) {\n"
                       uu____2368
                   else ());
                  (let uu____2373 =
                     let uu____2380 = FStar_Syntax_Embeddings.type_of e_arg
                        in
                     let uu____2381 = FStar_Syntax_Embeddings.type_of e_res
                        in
                     FStar_TypeChecker_TcTerm.tc_tactic uu____2380 uu____2381
                       env tactic
                      in
                   match uu____2373 with
                   | (uu____2388,uu____2389,g) ->
                       ((let uu____2392 = FStar_ST.op_Bang tacdbg  in
                         if uu____2392
                         then FStar_Util.print_string "}\n"
                         else ());
                        (let env1 =
                           let uu___198_2420 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___198_2420.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___198_2420.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___198_2420.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___198_2420.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___198_2420.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___198_2420.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___198_2420.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___198_2420.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___198_2420.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___198_2420.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___198_2420.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___198_2420.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___198_2420.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___198_2420.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___198_2420.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___198_2420.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___198_2420.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___198_2420.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___198_2420.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___198_2420.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes = true;
                             FStar_TypeChecker_Env.phase1 =
                               (uu___198_2420.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___198_2420.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___198_2420.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___198_2420.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___198_2420.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___198_2420.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___198_2420.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___198_2420.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___198_2420.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___198_2420.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___198_2420.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___198_2420.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___198_2420.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___198_2420.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___198_2420.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___198_2420.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___198_2420.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___198_2420.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___198_2420.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___198_2420.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___198_2420.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___198_2420.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___198_2420.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___198_2420.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                         FStar_Errors.stop_if_err ();
                         (let tau =
                            unembed_tactic_1 e_arg e_res tactic
                              FStar_Syntax_Embeddings.id_norm_cb
                             in
                          FStar_ST.op_Colon_Equals
                            FStar_Reflection_Basic.env_hook
                            (FStar_Pervasives_Native.Some env1);
                          (let uu____2455 =
                             FStar_Util.record_time
                               (fun uu____2467  ->
                                  let uu____2468 = tau arg  in
                                  FStar_Tactics_Basic.run_safe uu____2468 ps)
                              in
                           match uu____2455 with
                           | (res,ms) ->
                               ((let uu____2486 = FStar_ST.op_Bang tacdbg  in
                                 if uu____2486
                                 then FStar_Util.print_string "}\n"
                                 else ());
                                (let uu____2514 =
                                   (FStar_ST.op_Bang tacdbg) ||
                                     (FStar_Options.tactics_info ())
                                    in
                                 if uu____2514
                                 then
                                   let uu____2538 =
                                     FStar_Syntax_Print.term_to_string tactic
                                      in
                                   let uu____2540 =
                                     FStar_Util.string_of_int ms  in
                                   let uu____2542 =
                                     FStar_Syntax_Print.lid_to_string
                                       env1.FStar_TypeChecker_Env.curmodule
                                      in
                                   FStar_Util.print3
                                     "Tactic %s ran in %s ms (%s)\n"
                                     uu____2538 uu____2540 uu____2542
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success (ret1,ps1) ->
                                     (FStar_List.iter
                                        (fun g1  ->
                                           let uu____2560 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____2560
                                           then
                                             let uu____2563 =
                                               let uu____2565 =
                                                 FStar_Tactics_Types.goal_env
                                                   g1
                                                  in
                                               let uu____2566 =
                                                 FStar_Tactics_Types.goal_witness
                                                   g1
                                                  in
                                               FStar_TypeChecker_Rel.teq_nosmt_force
                                                 uu____2565 uu____2566
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____2563
                                              then ()
                                              else
                                                (let uu____2570 =
                                                   let uu____2572 =
                                                     let uu____2574 =
                                                       FStar_Tactics_Types.goal_witness
                                                         g1
                                                        in
                                                     FStar_Syntax_Print.term_to_string
                                                       uu____2574
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____2572
                                                    in
                                                 failwith uu____2570))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let uu____2579 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____2579
                                       then
                                         let uu____2603 =
                                           FStar_Common.string_of_list
                                             (fun imp  ->
                                                FStar_Syntax_Print.ctx_uvar_to_string
                                                  imp.FStar_TypeChecker_Common.imp_uvar)
                                             ps1.FStar_Tactics_Types.all_implicits
                                            in
                                         FStar_Util.print1
                                           "About to check tactic implicits: %s\n"
                                           uu____2603
                                       else ());
                                      (let g1 =
                                         let uu___224_2611 =
                                           FStar_TypeChecker_Env.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Common.guard_f =
                                             (uu___224_2611.FStar_TypeChecker_Common.guard_f);
                                           FStar_TypeChecker_Common.deferred
                                             =
                                             (uu___224_2611.FStar_TypeChecker_Common.deferred);
                                           FStar_TypeChecker_Common.univ_ineqs
                                             =
                                             (uu___224_2611.FStar_TypeChecker_Common.univ_ineqs);
                                           FStar_TypeChecker_Common.implicits
                                             =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           env1 g1
                                          in
                                       (let uu____2614 =
                                          FStar_ST.op_Bang tacdbg  in
                                        if uu____2614
                                        then
                                          let uu____2638 =
                                            FStar_Util.string_of_int
                                              (FStar_List.length
                                                 ps1.FStar_Tactics_Types.all_implicits)
                                             in
                                          let uu____2640 =
                                            FStar_Common.string_of_list
                                              (fun imp  ->
                                                 FStar_Syntax_Print.ctx_uvar_to_string
                                                   imp.FStar_TypeChecker_Common.imp_uvar)
                                              ps1.FStar_Tactics_Types.all_implicits
                                             in
                                          FStar_Util.print2
                                            "Checked %s implicits (1): %s\n"
                                            uu____2638 uu____2640
                                        else ());
                                       (let g3 =
                                          FStar_TypeChecker_Rel.resolve_implicits_tac
                                            env1 g2
                                           in
                                        (let uu____2649 =
                                           FStar_ST.op_Bang tacdbg  in
                                         if uu____2649
                                         then
                                           let uu____2673 =
                                             FStar_Util.string_of_int
                                               (FStar_List.length
                                                  ps1.FStar_Tactics_Types.all_implicits)
                                              in
                                           let uu____2675 =
                                             FStar_Common.string_of_list
                                               (fun imp  ->
                                                  FStar_Syntax_Print.ctx_uvar_to_string
                                                    imp.FStar_TypeChecker_Common.imp_uvar)
                                               ps1.FStar_Tactics_Types.all_implicits
                                              in
                                           FStar_Util.print2
                                             "Checked %s implicits (2): %s\n"
                                             uu____2673 uu____2675
                                         else ());
                                        report_implicits rng_goal
                                          g3.FStar_TypeChecker_Common.implicits;
                                        (let uu____2684 =
                                           FStar_ST.op_Bang tacdbg  in
                                         if uu____2684
                                         then
                                           let uu____2708 =
                                             let uu____2709 =
                                               FStar_TypeChecker_Cfg.psc_subst
                                                 ps1.FStar_Tactics_Types.psc
                                                in
                                             FStar_Tactics_Types.subst_proof_state
                                               uu____2709 ps1
                                              in
                                           FStar_Tactics_Basic.do_dump_proofstate
                                             uu____2708 "at the finish line"
                                         else ());
                                        ((FStar_List.append
                                            ps1.FStar_Tactics_Types.goals
                                            ps1.FStar_Tactics_Types.smt_goals),
                                          ret1))))
                                 | FStar_Tactics_Result.Failed (e,ps1) ->
                                     ((let uu____2718 =
                                         let uu____2719 =
                                           FStar_TypeChecker_Cfg.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____2719 ps1
                                          in
                                       FStar_Tactics_Basic.do_dump_proofstate
                                         uu____2718 "at the time of failure");
                                      (let texn_to_string e1 =
                                         match e1 with
                                         | FStar_Tactics_Types.TacticFailure
                                             s -> s
                                         | FStar_Tactics_Types.EExn t ->
                                             let uu____2732 =
                                               FStar_Syntax_Print.term_to_string
                                                 t
                                                in
                                             Prims.op_Hat
                                               "uncaught exception: "
                                               uu____2732
                                         | e2 -> FStar_Exn.raise e2  in
                                       let uu____2737 =
                                         let uu____2743 =
                                           let uu____2745 = texn_to_string e
                                              in
                                           FStar_Util.format1
                                             "user tactic failed: %s"
                                             uu____2745
                                            in
                                         (FStar_Errors.Fatal_UserTacticFailure,
                                           uu____2743)
                                          in
                                       FStar_Errors.raise_error uu____2737
                                         ps1.FStar_Tactics_Types.entry_range)))))))))
  
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
              let uu____2794 = FStar_Range.use_range rng_goal  in
              let uu____2795 = FStar_Range.use_range rng_tac  in
              FStar_Range.range_of_rng uu____2794 uu____2795  in
            let uu____2796 =
              FStar_Tactics_Basic.proofstate_of_goal_ty rng env typ  in
            match uu____2796 with
            | (ps,w) ->
                let uu____2809 =
                  run_tactic_on_ps rng_tac rng_goal
                    FStar_Syntax_Embeddings.e_unit ()
                    FStar_Syntax_Embeddings.e_unit tactic env ps
                   in
                (match uu____2809 with | (gs,_res) -> (gs, w))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2839 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2850 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2861 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2920 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2964 -> false
  
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3022 -> false
  
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____3065 . 'Auu____3065 -> 'Auu____3065 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3095 = FStar_Syntax_Util.head_and_args t  in
        match uu____3095 with
        | (hd1,args) ->
            let uu____3138 =
              let uu____3153 =
                let uu____3154 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3154.FStar_Syntax_Syntax.n  in
              (uu____3153, args)  in
            (match uu____3138 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(tactic,FStar_Pervasives_Native.None )::(assertion,FStar_Pervasives_Native.None
                                                            )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3216 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3216 with
                       | (gs,uu____3224) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3231 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3231 with
                       | (gs,uu____3239) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3282 =
                        let uu____3289 =
                          let uu____3292 =
                            let uu____3293 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3293
                             in
                          [uu____3292]  in
                        (FStar_Syntax_Util.t_true, uu____3289)  in
                      Simplified uu____3282
                  | Both  ->
                      let uu____3304 =
                        let uu____3313 =
                          let uu____3316 =
                            let uu____3317 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3317
                             in
                          [uu____3316]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3313)  in
                      Dual uu____3304
                  | Neg  -> Simplified (assertion, []))
             | uu____3330 -> Unchanged t)
  
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___0_3422  ->
      match uu___0_3422 with
      | Unchanged t -> let uu____3428 = f t  in Unchanged uu____3428
      | Simplified (t,gs) ->
          let uu____3435 = let uu____3442 = f t  in (uu____3442, gs)  in
          Simplified uu____3435
      | Dual (tn,tp,gs) ->
          let uu____3452 =
            let uu____3461 = f tn  in
            let uu____3462 = f tp  in (uu____3461, uu____3462, gs)  in
          Dual uu____3452
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3526 = f t1 t2  in Unchanged uu____3526
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3538 = let uu____3545 = f t1 t2  in (uu____3545, gs)
               in
            Simplified uu____3538
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3559 = let uu____3566 = f t1 t2  in (uu____3566, gs)
               in
            Simplified uu____3559
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3585 =
              let uu____3592 = f t1 t2  in
              (uu____3592, (FStar_List.append gs1 gs2))  in
            Simplified uu____3585
        | uu____3595 ->
            let uu____3604 = explode x  in
            (match uu____3604 with
             | (n1,p1,gs1) ->
                 let uu____3622 = explode y  in
                 (match uu____3622 with
                  | (n2,p2,gs2) ->
                      let uu____3640 =
                        let uu____3649 = f n1 n2  in
                        let uu____3650 = f p1 p2  in
                        (uu____3649, uu____3650, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3640))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3723 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3723
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3772  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3815 =
              let uu____3816 = FStar_Syntax_Subst.compress t  in
              uu____3816.FStar_Syntax_Syntax.n  in
            match uu____3815 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3828 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3828 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3854 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3854 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3874;
                   FStar_Syntax_Syntax.vars = uu____3875;_},(p,uu____3877)::
                 (q,uu____3879)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3937 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3937 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3951 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3951.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3955;
                   FStar_Syntax_Syntax.vars = uu____3956;_},(p,uu____3958)::
                 (q,uu____3960)::[])
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
                  let uu____4018 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4018 p  in
                let r2 =
                  let uu____4020 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4020 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4027,Unchanged uu____4028) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4046 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4046.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4049 ->
                     let uu____4058 = explode r1  in
                     (match uu____4058 with
                      | (pn,pp,gs1) ->
                          let uu____4076 = explode r2  in
                          (match uu____4076 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4097 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4100 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4097
                                   uu____4100
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4164  ->
                       fun r  ->
                         match uu____4164 with
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
                let uu____4316 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4316 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4356  ->
                            match uu____4356 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4378 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___494_4410 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___494_4410.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___494_4410.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4378 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4438 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4438.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4484 = traverse f pol e t1  in
                let uu____4489 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4489 uu____4484
            | FStar_Syntax_Syntax.Tm_match (sc,brs) ->
                let uu____4564 = traverse f pol e sc  in
                let uu____4569 =
                  let uu____4588 =
                    FStar_List.map
                      (fun br  ->
                         let uu____4605 = FStar_Syntax_Subst.open_branch br
                            in
                         match uu____4605 with
                         | (pat,w,exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs
                                in
                             let r = traverse f pol e1 exp  in
                             let uu____4632 =
                               comb1
                                 (fun exp1  ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1))
                                in
                             uu____4632 r) brs
                     in
                  comb_list uu____4588  in
                comb2
                  (fun sc1  ->
                     fun brs1  -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____4564 uu____4569
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___526_4718 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___526_4718.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___526_4718.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4725 =
                f pol e
                  (let uu___532_4729 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___532_4729.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___532_4729.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4725
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___539_4739 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___539_4739.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___539_4739.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4740 = explode rp  in
              (match uu____4740 with
               | (uu____4749,p',gs') ->
                   Dual
                     ((let uu___546_4759 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___546_4759.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___546_4759.FStar_Syntax_Syntax.vars)
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
      (let uu____4804 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4804);
      (let uu____4829 = FStar_ST.op_Bang tacdbg  in
       if uu____4829
       then
         let uu____4853 =
           let uu____4855 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4855
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4858 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4853
           uu____4858
       else ());
      (let initial = (Prims.int_one, [])  in
       let uu____4893 =
         let uu____4902 = traverse by_tactic_interp Pos env goal  in
         match uu____4902 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4926 -> failwith "no"  in
       match uu____4893 with
       | (t',gs) ->
           ((let uu____4955 = FStar_ST.op_Bang tacdbg  in
             if uu____4955
             then
               let uu____4979 =
                 let uu____4981 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4981
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4984 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4979 uu____4984
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5039  ->
                    fun g  ->
                      match uu____5039 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____5088 =
                              let uu____5091 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____5092 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____5091 uu____5092  in
                            match uu____5088 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5093 =
                                  let uu____5099 =
                                    let uu____5101 =
                                      let uu____5103 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____5103
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5101
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5099)
                                   in
                                FStar_Errors.raise_error uu____5093
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5108 = FStar_ST.op_Bang tacdbg  in
                            if uu____5108
                            then
                              let uu____5132 = FStar_Util.string_of_int n1
                                 in
                              let uu____5134 =
                                let uu____5136 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____5136
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5132 uu____5134
                            else ());
                           (let label1 =
                              let uu____5142 =
                                let uu____5144 =
                                  FStar_Tactics_Types.get_label g  in
                                uu____5144 = ""  in
                              if uu____5142
                              then
                                let uu____5150 = FStar_Util.string_of_int n1
                                   in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____5150
                              else
                                (let uu____5155 =
                                   let uu____5157 =
                                     FStar_Util.string_of_int n1  in
                                   let uu____5159 =
                                     let uu____5161 =
                                       let uu____5163 =
                                         FStar_Tactics_Types.get_label g  in
                                       Prims.op_Hat uu____5163 ")"  in
                                     Prims.op_Hat " (" uu____5161  in
                                   Prims.op_Hat uu____5157 uu____5159  in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____5155)
                               in
                            let gt' =
                              FStar_TypeChecker_Util.label label1
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____5169 =
                              let uu____5178 =
                                let uu____5185 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____5185, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____5178 :: gs1  in
                            ((n1 + Prims.int_one), uu____5169)))) s gs
                in
             let uu____5202 = s1  in
             match uu____5202 with
             | (uu____5224,gs1) ->
                 let uu____5244 =
                   let uu____5251 = FStar_Options.peek ()  in
                   (env, t', uu____5251)  in
                 uu____5244 :: gs1)))
  
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
          let uu____5275 =
            let uu____5280 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____5281 =
              let uu____5282 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5282]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____5280 uu____5281  in
          uu____5275 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____5310 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5310);
           (let uu____5334 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____5334 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____5355 =
                        let uu____5358 = FStar_Tactics_Types.goal_env g  in
                        let uu____5359 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____5358 uu____5359  in
                      match uu____5355 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____5362 = FStar_ST.op_Bang tacdbg  in
                            if uu____5362
                            then
                              let uu____5386 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____5386
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
                            let uu____5401 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____5401 guard))
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
        ((let uu____5423 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____5423);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let ps =
            FStar_Tactics_Basic.proofstate_of_goals
              tau.FStar_Syntax_Syntax.pos env [] []
             in
          let uu____5449 =
            let uu____5458 =
              FStar_Syntax_Embeddings.e_list
                FStar_Reflection_Embeddings.e_sigelt
               in
            run_tactic_on_ps tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos FStar_Syntax_Embeddings.e_unit ()
              uu____5458 tau env ps
             in
          match uu____5449 with
          | (gs,sigelts) ->
              ((let uu____5478 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____5483 =
                         let uu____5485 =
                           let uu____5488 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____5489 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____5488 uu____5489  in
                         FStar_Option.isSome uu____5485  in
                       Prims.op_Negation uu____5483) gs
                   in
                if uu____5478
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                      "splice left open goals") typ.FStar_Syntax_Syntax.pos
                else ());
               (let uu____5496 = FStar_ST.op_Bang tacdbg  in
                if uu____5496
                then
                  let uu____5520 =
                    FStar_Common.string_of_list
                      FStar_Syntax_Print.sigelt_to_string sigelts
                     in
                  FStar_Util.print1 "splice: got decls = %s\n" uu____5520
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
          ((let uu____5545 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5545);
           (let ps =
              FStar_Tactics_Basic.proofstate_of_goals
                tm.FStar_Syntax_Syntax.pos env [] []
               in
            let uu____5570 =
              run_tactic_on_ps tau.FStar_Syntax_Syntax.pos
                tm.FStar_Syntax_Syntax.pos FStar_Reflection_Embeddings.e_term
                tm FStar_Reflection_Embeddings.e_term tau env ps
               in
            match uu____5570 with | (gs,tm1) -> tm1))
  
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
            ((let uu____5608 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")
                 in
              FStar_ST.op_Colon_Equals tacdbg uu____5608);
             (let uu____5632 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None
                 in
              match uu____5632 with
              | (uvtm,uu____5651,g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ  in
                  let goal =
                    let uu____5669 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm
                       in
                    FStar_Syntax_Util.mk_squash u uu____5669  in
                  let uu____5670 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal
                     in
                  (match uu____5670 with
                   | (gs,w) ->
                       (FStar_List.iter
                          (fun g  ->
                             let uu____5691 =
                               let uu____5694 =
                                 FStar_Tactics_Types.goal_env g  in
                               let uu____5695 =
                                 FStar_Tactics_Types.goal_type g  in
                               getprop uu____5694 uu____5695  in
                             match uu____5691 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____5698 = FStar_ST.op_Bang tacdbg
                                      in
                                   if uu____5698
                                   then
                                     let uu____5722 =
                                       FStar_Syntax_Print.term_to_string vc
                                        in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____5722
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
                                   let uu____5737 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____5737 guard))
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
  