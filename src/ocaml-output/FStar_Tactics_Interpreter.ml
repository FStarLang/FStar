open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let mktot1' :
  'Auu____38 'Auu____39 'Auu____40 'Auu____41 .
    Prims.int ->
      Prims.string ->
        ('Auu____38 -> 'Auu____39) ->
          'Auu____38 FStar_Syntax_Embeddings.embedding ->
            'Auu____39 FStar_Syntax_Embeddings.embedding ->
              ('Auu____40 -> 'Auu____41) ->
                'Auu____40 FStar_TypeChecker_NBETerm.embedding ->
                  'Auu____41 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___354_108 =
                    FStar_Tactics_InterpFuns.mktot1 uarity nm f ea er nf ena
                      enr
                     in
                  let uu____109 =
                    FStar_Ident.lid_of_str
                      (Prims.strcat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____109;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___354_108.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___354_108.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___354_108.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___354_108.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___354_108.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___354_108.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___354_108.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot2' :
  'Auu____142 'Auu____143 'Auu____144 'Auu____145 'Auu____146 'Auu____147 .
    Prims.int ->
      Prims.string ->
        ('Auu____142 -> 'Auu____143 -> 'Auu____144) ->
          'Auu____142 FStar_Syntax_Embeddings.embedding ->
            'Auu____143 FStar_Syntax_Embeddings.embedding ->
              'Auu____144 FStar_Syntax_Embeddings.embedding ->
                ('Auu____145 -> 'Auu____146 -> 'Auu____147) ->
                  'Auu____145 FStar_TypeChecker_NBETerm.embedding ->
                    'Auu____146 FStar_TypeChecker_NBETerm.embedding ->
                      'Auu____147 FStar_TypeChecker_NBETerm.embedding ->
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
                      let uu___355_242 =
                        FStar_Tactics_InterpFuns.mktot2 uarity nm f ea eb er
                          nf ena enb enr
                         in
                      let uu____243 =
                        FStar_Ident.lid_of_str
                          (Prims.strcat "FStar.Tactics.Types." nm)
                         in
                      {
                        FStar_TypeChecker_Cfg.name = uu____243;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___355_242.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___355_242.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___355_242.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___355_242.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___355_242.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___355_242.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___355_242.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
  
let rec e_tactic_thunk :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____550 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____557  ->
         fun uu____558  ->
           fun uu____559  ->
             fun uu____560  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____593 =
               let uu____596 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____596 ()  in
             FStar_Pervasives_Native.Some uu____593) uu____550

and e_tactic_nbe_thunk :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____610 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____616  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____624 =
             let uu____627 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____627 ()  in
           FStar_Pervasives_Native.Some uu____624)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____610

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____642 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____652  ->
           fun uu____653  ->
             fun uu____654  ->
               fun uu____655  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____690 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____690) uu____642

and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____710 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____719  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____729 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____729)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____710

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____741  ->
    let uu____744 =
      let uu____747 =
        mktot1' (Prims.parse_int "0") "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____748 =
        let uu____751 =
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
        let uu____752 =
          let uu____755 =
            mktot1' (Prims.parse_int "0") "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe
             in
          let uu____756 =
            let uu____759 =
              mktot1' (Prims.parse_int "0") "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____760 =
              let uu____763 =
                let uu____764 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal
                   in
                let uu____769 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe
                   in
                mktot1' (Prims.parse_int "0") "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____764
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____769
                 in
              let uu____778 =
                let uu____781 =
                  let uu____782 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____787 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mktot1' (Prims.parse_int "0") "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____782
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____787
                   in
                let uu____796 =
                  let uu____799 =
                    mktot1' (Prims.parse_int "0") "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env
                     in
                  let uu____800 =
                    let uu____803 =
                      mktot1' (Prims.parse_int "0") "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term
                       in
                    let uu____804 =
                      let uu____807 =
                        mktot1' (Prims.parse_int "0") "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____808 =
                        let uu____811 =
                          mktot1' (Prims.parse_int "0") "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool
                           in
                        let uu____812 =
                          let uu____815 =
                            mktot1' (Prims.parse_int "0") "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string
                             in
                          let uu____816 =
                            let uu____819 =
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
                            let uu____820 =
                              let uu____823 =
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
                              let uu____880 =
                                let uu____883 =
                                  FStar_Tactics_InterpFuns.mktac2
                                    (Prims.parse_int "1") "fail"
                                    (fun uu____885  ->
                                       FStar_Tactics_Basic.fail)
                                    FStar_Syntax_Embeddings.e_any
                                    FStar_Syntax_Embeddings.e_string
                                    FStar_Syntax_Embeddings.e_any
                                    (fun uu____887  ->
                                       FStar_Tactics_Basic.fail)
                                    FStar_TypeChecker_NBETerm.e_any
                                    FStar_TypeChecker_NBETerm.e_string
                                    FStar_TypeChecker_NBETerm.e_any
                                   in
                                let uu____888 =
                                  let uu____891 =
                                    let uu____892 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Tactics_Embedding.e_goal
                                       in
                                    let uu____897 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Tactics_Embedding.e_goal_nbe
                                       in
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "set_goals"
                                      FStar_Tactics_Basic.set_goals uu____892
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.set_goals uu____897
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____906 =
                                    let uu____909 =
                                      let uu____910 =
                                        FStar_Syntax_Embeddings.e_list
                                          FStar_Tactics_Embedding.e_goal
                                         in
                                      let uu____915 =
                                        FStar_TypeChecker_NBETerm.e_list
                                          FStar_Tactics_Embedding.e_goal_nbe
                                         in
                                      FStar_Tactics_InterpFuns.mktac1
                                        (Prims.parse_int "0") "set_smt_goals"
                                        FStar_Tactics_Basic.set_smt_goals
                                        uu____910
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.set_smt_goals
                                        uu____915
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____924 =
                                      let uu____927 =
                                        FStar_Tactics_InterpFuns.mktac1
                                          (Prims.parse_int "0") "trivial"
                                          FStar_Tactics_Basic.trivial
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Tactics_Basic.trivial
                                          FStar_TypeChecker_NBETerm.e_unit
                                          FStar_TypeChecker_NBETerm.e_unit
                                         in
                                      let uu____928 =
                                        let uu____931 =
                                          let uu____932 =
                                            e_tactic_thunk
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____937 =
                                            FStar_Syntax_Embeddings.e_either
                                              FStar_Syntax_Embeddings.e_string
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____944 =
                                            e_tactic_nbe_thunk
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          let uu____949 =
                                            FStar_TypeChecker_NBETerm.e_either
                                              FStar_TypeChecker_NBETerm.e_string
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          FStar_Tactics_InterpFuns.mktac2
                                            (Prims.parse_int "1") "catch"
                                            (fun uu____969  ->
                                               FStar_Tactics_Basic.catch)
                                            FStar_Syntax_Embeddings.e_any
                                            uu____932 uu____937
                                            (fun uu____971  ->
                                               FStar_Tactics_Basic.catch)
                                            FStar_TypeChecker_NBETerm.e_any
                                            uu____944 uu____949
                                           in
                                        let uu____972 =
                                          let uu____975 =
                                            let uu____976 =
                                              e_tactic_thunk
                                                FStar_Syntax_Embeddings.e_any
                                               in
                                            let uu____981 =
                                              FStar_Syntax_Embeddings.e_either
                                                FStar_Syntax_Embeddings.e_string
                                                FStar_Syntax_Embeddings.e_any
                                               in
                                            let uu____988 =
                                              e_tactic_nbe_thunk
                                                FStar_TypeChecker_NBETerm.e_any
                                               in
                                            let uu____993 =
                                              FStar_TypeChecker_NBETerm.e_either
                                                FStar_TypeChecker_NBETerm.e_string
                                                FStar_TypeChecker_NBETerm.e_any
                                               in
                                            FStar_Tactics_InterpFuns.mktac2
                                              (Prims.parse_int "1") "recover"
                                              (fun uu____1013  ->
                                                 FStar_Tactics_Basic.recover)
                                              FStar_Syntax_Embeddings.e_any
                                              uu____976 uu____981
                                              (fun uu____1015  ->
                                                 FStar_Tactics_Basic.recover)
                                              FStar_TypeChecker_NBETerm.e_any
                                              uu____988 uu____993
                                             in
                                          let uu____1016 =
                                            let uu____1019 =
                                              FStar_Tactics_InterpFuns.mktac1
                                                (Prims.parse_int "0") "intro"
                                                FStar_Tactics_Basic.intro
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Reflection_Embeddings.e_binder
                                                FStar_Tactics_Basic.intro
                                                FStar_TypeChecker_NBETerm.e_unit
                                                FStar_Reflection_NBEEmbeddings.e_binder
                                               in
                                            let uu____1020 =
                                              let uu____1023 =
                                                let uu____1024 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Reflection_Embeddings.e_binder
                                                    FStar_Reflection_Embeddings.e_binder
                                                   in
                                                let uu____1031 =
                                                  FStar_TypeChecker_NBETerm.e_tuple2
                                                    FStar_Reflection_NBEEmbeddings.e_binder
                                                    FStar_Reflection_NBEEmbeddings.e_binder
                                                   in
                                                FStar_Tactics_InterpFuns.mktac1
                                                  (Prims.parse_int "0")
                                                  "intro_rec"
                                                  FStar_Tactics_Basic.intro_rec
                                                  FStar_Syntax_Embeddings.e_unit
                                                  uu____1024
                                                  FStar_Tactics_Basic.intro_rec
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                  uu____1031
                                                 in
                                              let uu____1046 =
                                                let uu____1049 =
                                                  let uu____1050 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step
                                                     in
                                                  let uu____1055 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step
                                                     in
                                                  FStar_Tactics_InterpFuns.mktac1
                                                    (Prims.parse_int "0")
                                                    "norm"
                                                    FStar_Tactics_Basic.norm
                                                    uu____1050
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Tactics_Basic.norm
                                                    uu____1055
                                                    FStar_TypeChecker_NBETerm.e_unit
                                                   in
                                                let uu____1064 =
                                                  let uu____1067 =
                                                    let uu____1068 =
                                                      FStar_Syntax_Embeddings.e_list
                                                        FStar_Syntax_Embeddings.e_norm_step
                                                       in
                                                    let uu____1073 =
                                                      FStar_TypeChecker_NBETerm.e_list
                                                        FStar_TypeChecker_NBETerm.e_norm_step
                                                       in
                                                    FStar_Tactics_InterpFuns.mktac3
                                                      (Prims.parse_int "0")
                                                      "norm_term_env"
                                                      FStar_Tactics_Basic.norm_term_env
                                                      FStar_Reflection_Embeddings.e_env
                                                      uu____1068
                                                      FStar_Reflection_Embeddings.e_term
                                                      FStar_Reflection_Embeddings.e_term
                                                      FStar_Tactics_Basic.norm_term_env
                                                      FStar_Reflection_NBEEmbeddings.e_env
                                                      uu____1073
                                                      FStar_Reflection_NBEEmbeddings.e_term
                                                      FStar_Reflection_NBEEmbeddings.e_term
                                                     in
                                                  let uu____1082 =
                                                    let uu____1085 =
                                                      let uu____1086 =
                                                        FStar_Syntax_Embeddings.e_list
                                                          FStar_Syntax_Embeddings.e_norm_step
                                                         in
                                                      let uu____1091 =
                                                        FStar_TypeChecker_NBETerm.e_list
                                                          FStar_TypeChecker_NBETerm.e_norm_step
                                                         in
                                                      FStar_Tactics_InterpFuns.mktac2
                                                        (Prims.parse_int "0")
                                                        "norm_binder_type"
                                                        FStar_Tactics_Basic.norm_binder_type
                                                        uu____1086
                                                        FStar_Reflection_Embeddings.e_binder
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_Basic.norm_binder_type
                                                        uu____1091
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                       in
                                                    let uu____1100 =
                                                      let uu____1103 =
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
                                                      let uu____1104 =
                                                        let uu____1107 =
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
                                                        let uu____1108 =
                                                          let uu____1111 =
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
                                                          let uu____1112 =
                                                            let uu____1115 =
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
                                                            let uu____1116 =
                                                              let uu____1119
                                                                =
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
                                                              let uu____1120
                                                                =
                                                                let uu____1123
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
                                                                let uu____1124
                                                                  =
                                                                  let uu____1127
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
                                                                  let uu____1128
                                                                    =
                                                                    let uu____1131
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
                                                                    let uu____1132
                                                                    =
                                                                    let uu____1135
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
                                                                    let uu____1136
                                                                    =
                                                                    let uu____1139
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
                                                                    let uu____1140
                                                                    =
                                                                    let uu____1143
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
                                                                    let uu____1144
                                                                    =
                                                                    let uu____1147
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
                                                                    let uu____1148
                                                                    =
                                                                    let uu____1151
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
                                                                    let uu____1152
                                                                    =
                                                                    let uu____1155
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1158
                                                                     ->
                                                                    fun
                                                                    uu____1159
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1162
                                                                    =
                                                                    let uu____1165
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
                                                                    let uu____1166
                                                                    =
                                                                    let uu____1169
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
                                                                    let uu____1170
                                                                    =
                                                                    let uu____1173
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
                                                                    let uu____1174
                                                                    =
                                                                    let uu____1177
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
                                                                    let uu____1178
                                                                    =
                                                                    let uu____1181
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
                                                                    let uu____1182
                                                                    =
                                                                    let uu____1185
                                                                    =
                                                                    let uu____1186
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1191
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "t_pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1186
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1191
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1200
                                                                    =
                                                                    let uu____1203
                                                                    =
                                                                    let uu____1204
                                                                    =
                                                                    let uu____1216
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1216
                                                                     in
                                                                    let uu____1227
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1232
                                                                    =
                                                                    let uu____1244
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1244
                                                                     in
                                                                    let uu____1255
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1204
                                                                    uu____1227
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1232
                                                                    uu____1255
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1282
                                                                    =
                                                                    let uu____1285
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
                                                                    let uu____1286
                                                                    =
                                                                    let uu____1289
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
                                                                    let uu____1290
                                                                    =
                                                                    let uu____1293
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
                                                                    let uu____1294
                                                                    =
                                                                    let uu____1297
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
                                                                    let uu____1298
                                                                    =
                                                                    let uu____1301
                                                                    =
                                                                    let uu____1302
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1309
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
                                                                    uu____1302
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1309
                                                                     in
                                                                    let uu____1324
                                                                    =
                                                                    let uu____1327
                                                                    =
                                                                    let uu____1328
                                                                    =
                                                                    let uu____1337
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1337
                                                                     in
                                                                    let uu____1348
                                                                    =
                                                                    let uu____1357
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1357
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1328
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1348
                                                                     in
                                                                    let uu____1380
                                                                    =
                                                                    let uu____1383
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
                                                                    let uu____1384
                                                                    =
                                                                    let uu____1387
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
                                                                    let uu____1388
                                                                    =
                                                                    let uu____1391
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
                                                                    let uu____1392
                                                                    =
                                                                    let uu____1395
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
                                                                    let uu____1396
                                                                    =
                                                                    let uu____1399
                                                                    =
                                                                    let uu____1400
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1405
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1400
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1405
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1414
                                                                    =
                                                                    let uu____1417
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
                                                                    let uu____1418
                                                                    =
                                                                    let uu____1421
                                                                    =
                                                                    let uu____1422
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1427
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1422
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1427
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1436
                                                                    =
                                                                    let uu____1439
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
                                                                    let uu____1440
                                                                    =
                                                                    let uu____1443
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
                                                                    let uu____1444
                                                                    =
                                                                    let uu____1447
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
                                                                    let uu____1448
                                                                    =
                                                                    let uu____1451
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
                                                                    let uu____1452
                                                                    =
                                                                    let uu____1455
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
                                                                    let uu____1456
                                                                    =
                                                                    let uu____1459
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1462
                                                                     ->
                                                                    fun
                                                                    uu____1463
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1464
                                                                    =
                                                                    let uu____1467
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
                                                                    uu____1471
                                                                     ->
                                                                    fun
                                                                    uu____1472
                                                                     ->
                                                                    fun
                                                                    uu____1473
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____1467]
                                                                     in
                                                                    uu____1459
                                                                    ::
                                                                    uu____1464
                                                                     in
                                                                    uu____1455
                                                                    ::
                                                                    uu____1456
                                                                     in
                                                                    uu____1451
                                                                    ::
                                                                    uu____1452
                                                                     in
                                                                    uu____1447
                                                                    ::
                                                                    uu____1448
                                                                     in
                                                                    uu____1443
                                                                    ::
                                                                    uu____1444
                                                                     in
                                                                    uu____1439
                                                                    ::
                                                                    uu____1440
                                                                     in
                                                                    uu____1421
                                                                    ::
                                                                    uu____1436
                                                                     in
                                                                    uu____1417
                                                                    ::
                                                                    uu____1418
                                                                     in
                                                                    uu____1399
                                                                    ::
                                                                    uu____1414
                                                                     in
                                                                    uu____1395
                                                                    ::
                                                                    uu____1396
                                                                     in
                                                                    uu____1391
                                                                    ::
                                                                    uu____1392
                                                                     in
                                                                    uu____1387
                                                                    ::
                                                                    uu____1388
                                                                     in
                                                                    uu____1383
                                                                    ::
                                                                    uu____1384
                                                                     in
                                                                    uu____1327
                                                                    ::
                                                                    uu____1380
                                                                     in
                                                                    uu____1301
                                                                    ::
                                                                    uu____1324
                                                                     in
                                                                    uu____1297
                                                                    ::
                                                                    uu____1298
                                                                     in
                                                                    uu____1293
                                                                    ::
                                                                    uu____1294
                                                                     in
                                                                    uu____1289
                                                                    ::
                                                                    uu____1290
                                                                     in
                                                                    uu____1285
                                                                    ::
                                                                    uu____1286
                                                                     in
                                                                    uu____1203
                                                                    ::
                                                                    uu____1282
                                                                     in
                                                                    uu____1185
                                                                    ::
                                                                    uu____1200
                                                                     in
                                                                    uu____1181
                                                                    ::
                                                                    uu____1182
                                                                     in
                                                                    uu____1177
                                                                    ::
                                                                    uu____1178
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
                                                                    uu____1155
                                                                    ::
                                                                    uu____1162
                                                                     in
                                                                    uu____1151
                                                                    ::
                                                                    uu____1152
                                                                     in
                                                                    uu____1147
                                                                    ::
                                                                    uu____1148
                                                                     in
                                                                    uu____1143
                                                                    ::
                                                                    uu____1144
                                                                     in
                                                                    uu____1139
                                                                    ::
                                                                    uu____1140
                                                                     in
                                                                    uu____1135
                                                                    ::
                                                                    uu____1136
                                                                     in
                                                                    uu____1131
                                                                    ::
                                                                    uu____1132
                                                                     in
                                                                  uu____1127
                                                                    ::
                                                                    uu____1128
                                                                   in
                                                                uu____1123 ::
                                                                  uu____1124
                                                                 in
                                                              uu____1119 ::
                                                                uu____1120
                                                               in
                                                            uu____1115 ::
                                                              uu____1116
                                                             in
                                                          uu____1111 ::
                                                            uu____1112
                                                           in
                                                        uu____1107 ::
                                                          uu____1108
                                                         in
                                                      uu____1103 ::
                                                        uu____1104
                                                       in
                                                    uu____1085 :: uu____1100
                                                     in
                                                  uu____1067 :: uu____1082
                                                   in
                                                uu____1049 :: uu____1064  in
                                              uu____1023 :: uu____1046  in
                                            uu____1019 :: uu____1020  in
                                          uu____975 :: uu____1016  in
                                        uu____931 :: uu____972  in
                                      uu____927 :: uu____928  in
                                    uu____909 :: uu____924  in
                                  uu____891 :: uu____906  in
                                uu____883 :: uu____888  in
                              uu____823 :: uu____880  in
                            uu____819 :: uu____820  in
                          uu____815 :: uu____816  in
                        uu____811 :: uu____812  in
                      uu____807 :: uu____808  in
                    uu____803 :: uu____804  in
                  uu____799 :: uu____800  in
                uu____781 :: uu____796  in
              uu____763 :: uu____778  in
            uu____759 :: uu____760  in
          uu____755 :: uu____756  in
        uu____751 :: uu____752  in
      uu____747 :: uu____748  in
    let uu____1474 =
      let uu____1477 = FStar_Tactics_InterpFuns.native_tactics_steps ()  in
      FStar_List.append FStar_Reflection_Interpreter.reflection_primops
        uu____1477
       in
    FStar_List.append uu____744 uu____1474

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
              let uu____1498 =
                let uu____1503 =
                  let uu____1504 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____1504]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____1503  in
              uu____1498 FStar_Pervasives_Native.None rng  in
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
               let uu____1561 =
                 let uu____1566 =
                   let uu____1567 =
                     let uu____1576 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1576  in
                   [uu____1567]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1566  in
               uu____1561 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1621 = FStar_Options.tactics_nbe ()  in
               if uu____1621
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____1640 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____1640)
             else ();
             (let result =
                let uu____1643 = primitive_steps ()  in
                norm_f uu____1643 steps
                  proof_state.FStar_Tactics_Types.main_context tm
                 in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____1647 = FStar_Syntax_Print.term_to_string result
                    in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____1647)
              else ();
              (let res =
                 let uu____1654 = FStar_Tactics_Embedding.e_result eb  in
                 FStar_Tactics_InterpFuns.unembed uu____1654 result ncb  in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b,ps)) ->
                   let uu____1669 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1669
                     (fun uu____1673  -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (msg,ps)) ->
                   let uu____1678 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1678
                     (fun uu____1682  -> FStar_Tactics_Basic.fail msg)
               | FStar_Pervasives_Native.None  ->
                   let uu____1685 =
                     let uu____1690 =
                       let uu____1691 =
                         FStar_Syntax_Print.term_to_string result  in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____1691
                        in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____1690)  in
                   FStar_Errors.raise_error uu____1685
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
              let uu____1705 =
                let uu____1706 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____1706]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1705  in
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
               let uu____1732 =
                 let uu____1733 =
                   let uu____1738 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1738  in
                 [uu____1733]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1732
                in
             let res =
               let uu____1752 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1752 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1765 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1765
                   (fun uu____1769  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____1774 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1774
                   (fun uu____1778  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____1781 =
                   let uu____1786 =
                     let uu____1787 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1787
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1786)  in
                 FStar_Errors.raise_error uu____1781
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
                 let uu____1817 =
                   let uu____1822 =
                     let uu____1823 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____1823]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1822  in
                 uu____1817 FStar_Pervasives_Native.None rng  in
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
      let em uu____1904 uu____1905 uu____1906 uu____1907 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n1 =
        let uu____1975 = unembed_tactic_1_alt ea er t0 n1  in
        match uu____1975 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____2017 = f x  in FStar_Tactics_Basic.run uu____2017))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____2033 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____2033

let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____2070 =
               let uu____2071 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____2072 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2071 uu____2072 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2070, rng)) is
         in
      FStar_Errors.add_errors errs; FStar_Errors.stop_if_err ()
  
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
            (let uu____2112 = FStar_ST.op_Bang tacdbg  in
             if uu____2112
             then
               let uu____2132 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____2132
             else ());
            (let uu____2134 = FStar_TypeChecker_TcTerm.tc_tactic env tactic
                in
             match uu____2134 with
             | (uu____2147,uu____2148,g) ->
                 ((let uu____2151 = FStar_ST.op_Bang tacdbg  in
                   if uu____2151 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_1 FStar_Syntax_Embeddings.e_unit
                       FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb
                      in
                   let uu____2181 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____2181 with
                   | (env1,uu____2195) ->
                       let env2 =
                         let uu___356_2201 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___356_2201.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___356_2201.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___356_2201.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___356_2201.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___356_2201.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___356_2201.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___356_2201.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___356_2201.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___356_2201.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___356_2201.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___356_2201.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___356_2201.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___356_2201.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___356_2201.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___356_2201.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___356_2201.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___356_2201.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___356_2201.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___356_2201.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___356_2201.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___356_2201.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___356_2201.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___356_2201.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___356_2201.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___356_2201.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___356_2201.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___356_2201.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___356_2201.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___356_2201.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___356_2201.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___356_2201.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___356_2201.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___356_2201.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___356_2201.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___356_2201.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___356_2201.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___356_2201.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___356_2201.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___356_2201.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___356_2201.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___356_2201.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___356_2201.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___357_2203 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___357_2203.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___357_2203.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___357_2203.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___357_2203.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___357_2203.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___357_2203.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___357_2203.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___357_2203.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___357_2203.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___357_2203.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___357_2203.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___357_2203.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___357_2203.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___357_2203.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___357_2203.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___357_2203.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___357_2203.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___357_2203.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___357_2203.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___357_2203.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___357_2203.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___357_2203.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___357_2203.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___357_2203.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___357_2203.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___357_2203.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___357_2203.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___357_2203.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___357_2203.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___357_2203.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___357_2203.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___357_2203.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___357_2203.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___357_2203.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___357_2203.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___357_2203.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___357_2203.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___357_2203.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___357_2203.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___357_2203.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___357_2203.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___357_2203.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___358_2205 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___358_2205.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___358_2205.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___358_2205.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___358_2205.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___358_2205.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___358_2205.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___358_2205.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___358_2205.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___358_2205.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___358_2205.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___358_2205.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___358_2205.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___358_2205.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___358_2205.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___358_2205.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___358_2205.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___358_2205.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___358_2205.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___358_2205.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___358_2205.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___358_2205.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___358_2205.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___358_2205.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___358_2205.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___358_2205.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___358_2205.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___358_2205.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___358_2205.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___358_2205.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___358_2205.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___358_2205.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___358_2205.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___358_2205.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___358_2205.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___358_2205.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___358_2205.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___358_2205.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___358_2205.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___358_2205.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___358_2205.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___358_2205.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___358_2205.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____2207 = FStar_Range.use_range rng_goal  in
                         let uu____2208 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____2207 uu____2208  in
                       let uu____2209 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____2209 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____2247 = FStar_ST.op_Bang tacdbg  in
                              if uu____2247
                              then
                                let uu____2267 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____2267
                              else ());
                             (let uu____2269 =
                                FStar_Util.record_time
                                  (fun uu____2280  ->
                                     let uu____2281 = tau ()  in
                                     FStar_Tactics_Basic.run_safe uu____2281
                                       ps)
                                 in
                              match uu____2269 with
                              | (res,ms) ->
                                  ((let uu____2297 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____2297
                                    then FStar_Util.print_string "}\n"
                                    else ());
                                   (let uu____2319 =
                                      (FStar_ST.op_Bang tacdbg) ||
                                        (FStar_Options.tactics_info ())
                                       in
                                    if uu____2319
                                    then
                                      let uu____2339 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____2340 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____2341 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "Tactic %s ran in %s ms (%s)\n"
                                        uu____2339 uu____2340 uu____2341
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____2349,ps1) ->
                                        ((let uu____2352 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2352
                                          then
                                            let uu____2372 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____2372
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____2379 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____2379
                                              then
                                                let uu____2380 =
                                                  let uu____2381 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____2382 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt_force
                                                    uu____2381 uu____2382
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____2380
                                                 then ()
                                                 else
                                                   (let uu____2384 =
                                                      let uu____2385 =
                                                        let uu____2386 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____2386
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____2385
                                                       in
                                                    failwith uu____2384))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____2389 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2389
                                          then
                                            let uu____2409 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____2409
                                          else ());
                                         (let g1 =
                                            let uu___359_2414 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___359_2414.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___359_2414.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___359_2414.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____2417 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____2417
                                           then
                                             let uu____2437 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits)
                                                in
                                             let uu____2438 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____2437 uu____2438
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____2444 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2444
                                            then
                                              let uu____2464 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits)
                                                 in
                                              let uu____2465 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____2464 uu____2465
                                            else ());
                                           report_implicits rng_goal
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____2471 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2471
                                            then
                                              let uu____2491 =
                                                let uu____2492 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc
                                                   in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____2492 ps1
                                                 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____2491
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____2499 =
                                            let uu____2500 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____2500 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____2499
                                            "at the time of failure");
                                         (let uu____2501 =
                                            let uu____2506 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____2506)
                                             in
                                          FStar_Errors.raise_error uu____2501
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2518 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2524 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2530 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2585 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2625 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2679 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____2720 . 'Auu____2720 -> 'Auu____2720 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____2748 = FStar_Syntax_Util.head_and_args t  in
        match uu____2748 with
        | (hd1,args) ->
            let uu____2791 =
              let uu____2806 =
                let uu____2807 = FStar_Syntax_Util.un_uinst hd1  in
                uu____2807.FStar_Syntax_Syntax.n  in
              (uu____2806, args)  in
            (match uu____2791 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2822))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2885 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2885 with
                       | (gs,uu____2893) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____2900 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2900 with
                       | (gs,uu____2908) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2951 =
                        let uu____2958 =
                          let uu____2961 =
                            let uu____2962 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2962
                             in
                          [uu____2961]  in
                        (FStar_Syntax_Util.t_true, uu____2958)  in
                      Simplified uu____2951
                  | Both  ->
                      let uu____2973 =
                        let uu____2982 =
                          let uu____2985 =
                            let uu____2986 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2986
                             in
                          [uu____2985]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____2982)  in
                      Dual uu____2973
                  | Neg  -> Simplified (assertion, []))
             | uu____2999 -> Unchanged t)
  
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
    fun uu___353_3089  ->
      match uu___353_3089 with
      | Unchanged t -> let uu____3095 = f t  in Unchanged uu____3095
      | Simplified (t,gs) ->
          let uu____3102 = let uu____3109 = f t  in (uu____3109, gs)  in
          Simplified uu____3102
      | Dual (tn,tp,gs) ->
          let uu____3119 =
            let uu____3128 = f tn  in
            let uu____3129 = f tp  in (uu____3128, uu____3129, gs)  in
          Dual uu____3119
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3192 = f t1 t2  in Unchanged uu____3192
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3204 = let uu____3211 = f t1 t2  in (uu____3211, gs)
               in
            Simplified uu____3204
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3225 = let uu____3232 = f t1 t2  in (uu____3232, gs)
               in
            Simplified uu____3225
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3251 =
              let uu____3258 = f t1 t2  in
              (uu____3258, (FStar_List.append gs1 gs2))  in
            Simplified uu____3251
        | uu____3261 ->
            let uu____3270 = explode x  in
            (match uu____3270 with
             | (n1,p1,gs1) ->
                 let uu____3288 = explode y  in
                 (match uu____3288 with
                  | (n2,p2,gs2) ->
                      let uu____3306 =
                        let uu____3315 = f n1 n2  in
                        let uu____3316 = f p1 p2  in
                        (uu____3315, uu____3316, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3306))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3388 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3388
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3436  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3478 =
              let uu____3479 = FStar_Syntax_Subst.compress t  in
              uu____3479.FStar_Syntax_Syntax.n  in
            match uu____3478 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3491 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3491 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3517 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3517 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3537;
                   FStar_Syntax_Syntax.vars = uu____3538;_},(p,uu____3540)::
                 (q,uu____3542)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3598 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3598
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3601 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3601 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3615 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3615.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3619;
                   FStar_Syntax_Syntax.vars = uu____3620;_},(p,uu____3622)::
                 (q,uu____3624)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3680 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3680
                   in
                let xq =
                  let uu____3682 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3682
                   in
                let r1 =
                  let uu____3684 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3684 p  in
                let r2 =
                  let uu____3686 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3686 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3693,Unchanged uu____3694) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3712 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3712.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3715 ->
                     let uu____3724 = explode r1  in
                     (match uu____3724 with
                      | (pn,pp,gs1) ->
                          let uu____3742 = explode r2  in
                          (match uu____3742 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3763 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3766 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3763
                                   uu____3766
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____3830  ->
                       fun r  ->
                         match uu____3830 with
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
                let uu____3982 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____3982 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4022  ->
                            match uu____4022 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4044 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___360_4076 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___360_4076.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___360_4076.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4044 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4104 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4104.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4150 = traverse f pol e t1  in
                let uu____4155 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4155 uu____4150
            | FStar_Syntax_Syntax.Tm_match (sc,brs) ->
                let uu____4230 = traverse f pol e sc  in
                let uu____4235 =
                  let uu____4254 =
                    FStar_List.map
                      (fun br  ->
                         let uu____4271 = FStar_Syntax_Subst.open_branch br
                            in
                         match uu____4271 with
                         | (pat,w,exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs
                                in
                             let r = traverse f pol e1 exp  in
                             let uu____4298 =
                               comb1
                                 (fun exp1  ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1))
                                in
                             uu____4298 r) brs
                     in
                  comb_list uu____4254  in
                comb2
                  (fun sc1  ->
                     fun brs1  -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____4230 uu____4235
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___361_4384 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___361_4384.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___361_4384.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4391 =
                f pol e
                  (let uu___362_4395 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___362_4395.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___362_4395.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4391
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___363_4405 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___363_4405.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___363_4405.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4406 = explode rp  in
              (match uu____4406 with
               | (uu____4415,p',gs') ->
                   Dual
                     ((let uu___364_4425 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___364_4425.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___364_4425.FStar_Syntax_Syntax.vars)
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
      (let uu____4468 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4468);
      (let uu____4489 = FStar_ST.op_Bang tacdbg  in
       if uu____4489
       then
         let uu____4509 =
           let uu____4510 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4510
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4511 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4509
           uu____4511
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4540 =
         let uu____4549 = traverse by_tactic_interp Pos env goal  in
         match uu____4549 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4573 -> failwith "no"  in
       match uu____4540 with
       | (t',gs) ->
           ((let uu____4601 = FStar_ST.op_Bang tacdbg  in
             if uu____4601
             then
               let uu____4621 =
                 let uu____4622 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4622
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4623 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4621 uu____4623
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4672  ->
                    fun g  ->
                      match uu____4672 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4717 =
                              let uu____4720 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____4721 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____4720 uu____4721  in
                            match uu____4717 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4722 =
                                  let uu____4727 =
                                    let uu____4728 =
                                      let uu____4729 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____4729
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____4728
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____4727)
                                   in
                                FStar_Errors.raise_error uu____4722
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4732 = FStar_ST.op_Bang tacdbg  in
                            if uu____4732
                            then
                              let uu____4752 = FStar_Util.string_of_int n1
                                 in
                              let uu____4753 =
                                let uu____4754 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____4754
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4752 uu____4753
                            else ());
                           (let label1 =
                              let uu____4757 =
                                let uu____4758 =
                                  FStar_Tactics_Types.get_label g  in
                                uu____4758 = ""  in
                              if uu____4757
                              then
                                let uu____4759 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4759
                              else
                                (let uu____4761 =
                                   let uu____4762 =
                                     FStar_Util.string_of_int n1  in
                                   let uu____4763 =
                                     let uu____4764 =
                                       let uu____4765 =
                                         FStar_Tactics_Types.get_label g  in
                                       Prims.strcat uu____4765 ")"  in
                                     Prims.strcat " (" uu____4764  in
                                   Prims.strcat uu____4762 uu____4763  in
                                 Prims.strcat "Could not prove goal #"
                                   uu____4761)
                               in
                            let gt' =
                              FStar_TypeChecker_Util.label label1
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____4767 =
                              let uu____4776 =
                                let uu____4783 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____4783, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____4776 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____4767)))) s
                 gs
                in
             let uu____4798 = s1  in
             match uu____4798 with
             | (uu____4819,gs1) ->
                 let uu____4837 =
                   let uu____4844 = FStar_Options.peek ()  in
                   (env, t', uu____4844)  in
                 uu____4837 :: gs1)))
  
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
          let uu____4866 =
            let uu____4871 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____4872 =
              let uu____4873 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4873]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____4871 uu____4872  in
          uu____4866 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____4902 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____4902);
           (let uu____4922 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____4922 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____4943 =
                        let uu____4946 = FStar_Tactics_Types.goal_env g  in
                        let uu____4947 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____4946 uu____4947  in
                      match uu____4943 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____4950 = FStar_ST.op_Bang tacdbg  in
                            if uu____4950
                            then
                              let uu____4970 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____4970
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____4981 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____4981 guard))
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
        ((let uu____4998 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____4998);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____5019 =
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos tau env typ
             in
          match uu____5019 with
          | (gs,w) ->
              ((let uu____5035 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____5039 =
                         let uu____5040 =
                           let uu____5043 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____5044 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____5043 uu____5044  in
                         FStar_Option.isSome uu____5040  in
                       Prims.op_Negation uu____5039) gs
                   in
                if uu____5035
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
                (let uu____5048 = FStar_ST.op_Bang tacdbg  in
                 if uu____5048
                 then
                   let uu____5068 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____5068
                 else ());
                (let uu____5070 =
                   let uu____5075 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____5075 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____5070 with
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
            ((let uu____5115 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")
                 in
              FStar_ST.op_Colon_Equals tacdbg uu____5115);
             (let uu____5135 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                 in
              match uu____5135 with
              | (uvtm,uu____5149,g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ  in
                  let goal =
                    let uu____5167 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm
                       in
                    FStar_Syntax_Util.mk_squash u uu____5167  in
                  let uu____5168 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal
                     in
                  (match uu____5168 with
                   | (gs,w) ->
                       (FStar_List.iter
                          (fun g  ->
                             let uu____5189 =
                               let uu____5192 =
                                 FStar_Tactics_Types.goal_env g  in
                               let uu____5193 =
                                 FStar_Tactics_Types.goal_type g  in
                               getprop uu____5192 uu____5193  in
                             match uu____5189 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____5196 = FStar_ST.op_Bang tacdbg
                                      in
                                   if uu____5196
                                   then
                                     let uu____5216 =
                                       FStar_Syntax_Print.term_to_string vc
                                        in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____5216
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
                                   let uu____5227 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____5227 guard))
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
  