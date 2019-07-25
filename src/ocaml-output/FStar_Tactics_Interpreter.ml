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
    let uu____663 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____670  ->
         fun uu____671  ->
           fun uu____672  ->
             fun uu____673  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____687 =
               let uu____690 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____690 ()  in
             FStar_Pervasives_Native.Some uu____687) uu____663

and e_tactic_nbe_thunk :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____702 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____708  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____717 =
             let uu____720 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____720 ()  in
           FStar_Pervasives_Native.Some uu____717)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____702

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____735 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____745  ->
           fun uu____746  ->
             fun uu____747  ->
               fun uu____748  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____764 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____764) uu____735

and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____782 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____791  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____802 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____802)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____782

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____814  ->
    let uu____817 =
      let uu____820 =
        mktot1'_psc Prims.int_zero "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____823 =
        let uu____826 =
          mktot1'_psc Prims.int_zero "set_ps_psc"
            FStar_Tactics_Types.set_ps_psc
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Types.set_ps_psc
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_Tactics_Embedding.e_proofstate_nbe
           in
        let uu____829 =
          let uu____832 =
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
          let uu____835 =
            let uu____838 =
              mktot1' Prims.int_zero "incr_depth"
                FStar_Tactics_Types.incr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.incr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____841 =
              let uu____844 =
                mktot1' Prims.int_zero "decr_depth"
                  FStar_Tactics_Types.decr_depth
                  FStar_Tactics_Embedding.e_proofstate
                  FStar_Tactics_Embedding.e_proofstate
                  FStar_Tactics_Types.decr_depth
                  FStar_Tactics_Embedding.e_proofstate_nbe
                  FStar_Tactics_Embedding.e_proofstate_nbe
                 in
              let uu____847 =
                let uu____850 =
                  let uu____851 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____856 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mktot1' Prims.int_zero "goals_of"
                    FStar_Tactics_Types.goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____851
                    FStar_Tactics_Types.goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____856
                   in
                let uu____867 =
                  let uu____870 =
                    let uu____871 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Tactics_Embedding.e_goal
                       in
                    let uu____876 =
                      FStar_TypeChecker_NBETerm.e_list
                        FStar_Tactics_Embedding.e_goal_nbe
                       in
                    mktot1' Prims.int_zero "smt_goals_of"
                      FStar_Tactics_Types.smt_goals_of
                      FStar_Tactics_Embedding.e_proofstate uu____871
                      FStar_Tactics_Types.smt_goals_of
                      FStar_Tactics_Embedding.e_proofstate_nbe uu____876
                     in
                  let uu____887 =
                    let uu____890 =
                      mktot1' Prims.int_zero "goal_env"
                        FStar_Tactics_Types.goal_env
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_env
                        FStar_Tactics_Types.goal_env
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_env
                       in
                    let uu____893 =
                      let uu____896 =
                        mktot1' Prims.int_zero "goal_type"
                          FStar_Tactics_Types.goal_type
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_type
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____899 =
                        let uu____902 =
                          mktot1' Prims.int_zero "goal_witness"
                            FStar_Tactics_Types.goal_witness
                            FStar_Tactics_Embedding.e_goal
                            FStar_Reflection_Embeddings.e_term
                            FStar_Tactics_Types.goal_witness
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_Reflection_NBEEmbeddings.e_term
                           in
                        let uu____905 =
                          let uu____908 =
                            mktot1' Prims.int_zero "is_guard"
                              FStar_Tactics_Types.is_guard
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_bool
                              FStar_Tactics_Types.is_guard
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_bool
                             in
                          let uu____913 =
                            let uu____916 =
                              mktot1' Prims.int_zero "get_label"
                                FStar_Tactics_Types.get_label
                                FStar_Tactics_Embedding.e_goal
                                FStar_Syntax_Embeddings.e_string
                                FStar_Tactics_Types.get_label
                                FStar_Tactics_Embedding.e_goal_nbe
                                FStar_TypeChecker_NBETerm.e_string
                               in
                            let uu____921 =
                              let uu____924 =
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
                              let uu____929 =
                                let uu____932 =
                                  FStar_Tactics_InterpFuns.mktot2
                                    Prims.int_zero "push_binder"
                                    (fun env  ->
                                       fun b  ->
                                         FStar_TypeChecker_Env.push_binders
                                           env [b])
                                    FStar_Reflection_Embeddings.e_env
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Reflection_Embeddings.e_env
                                    (fun env  ->
                                       fun b  ->
                                         FStar_TypeChecker_Env.push_binders
                                           env [b])
                                    FStar_Reflection_NBEEmbeddings.e_env
                                    FStar_Reflection_NBEEmbeddings.e_binder
                                    FStar_Reflection_NBEEmbeddings.e_env
                                   in
                                let uu____991 =
                                  let uu____994 =
                                    let uu____995 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Tactics_Embedding.e_goal
                                       in
                                    let uu____1000 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Tactics_Embedding.e_goal_nbe
                                       in
                                    FStar_Tactics_InterpFuns.mktac1
                                      Prims.int_zero "set_goals"
                                      FStar_Tactics_Basic.set_goals uu____995
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.set_goals
                                      uu____1000
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____1011 =
                                    let uu____1014 =
                                      let uu____1015 =
                                        FStar_Syntax_Embeddings.e_list
                                          FStar_Tactics_Embedding.e_goal
                                         in
                                      let uu____1020 =
                                        FStar_TypeChecker_NBETerm.e_list
                                          FStar_Tactics_Embedding.e_goal_nbe
                                         in
                                      FStar_Tactics_InterpFuns.mktac1
                                        Prims.int_zero "set_smt_goals"
                                        FStar_Tactics_Basic.set_smt_goals
                                        uu____1015
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.set_smt_goals
                                        uu____1020
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____1031 =
                                      let uu____1034 =
                                        FStar_Tactics_InterpFuns.mktac1
                                          Prims.int_zero "trivial"
                                          FStar_Tactics_Basic.trivial
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Tactics_Basic.trivial
                                          FStar_TypeChecker_NBETerm.e_unit
                                          FStar_TypeChecker_NBETerm.e_unit
                                         in
                                      let uu____1037 =
                                        let uu____1040 =
                                          let uu____1041 =
                                            e_tactic_thunk
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____1046 =
                                            FStar_Syntax_Embeddings.e_either
                                              FStar_Tactics_Embedding.e_exn
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____1053 =
                                            e_tactic_nbe_thunk
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          let uu____1058 =
                                            FStar_TypeChecker_NBETerm.e_either
                                              FStar_Tactics_Embedding.e_exn_nbe
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          FStar_Tactics_InterpFuns.mktac2
                                            Prims.int_one "catch"
                                            (fun uu____1080  ->
                                               FStar_Tactics_Basic.catch)
                                            FStar_Syntax_Embeddings.e_any
                                            uu____1041 uu____1046
                                            (fun uu____1082  ->
                                               FStar_Tactics_Basic.catch)
                                            FStar_TypeChecker_NBETerm.e_any
                                            uu____1053 uu____1058
                                           in
                                        let uu____1083 =
                                          let uu____1086 =
                                            let uu____1087 =
                                              e_tactic_thunk
                                                FStar_Syntax_Embeddings.e_any
                                               in
                                            let uu____1092 =
                                              FStar_Syntax_Embeddings.e_either
                                                FStar_Tactics_Embedding.e_exn
                                                FStar_Syntax_Embeddings.e_any
                                               in
                                            let uu____1099 =
                                              e_tactic_nbe_thunk
                                                FStar_TypeChecker_NBETerm.e_any
                                               in
                                            let uu____1104 =
                                              FStar_TypeChecker_NBETerm.e_either
                                                FStar_Tactics_Embedding.e_exn_nbe
                                                FStar_TypeChecker_NBETerm.e_any
                                               in
                                            FStar_Tactics_InterpFuns.mktac2
                                              Prims.int_one "recover"
                                              (fun uu____1126  ->
                                                 FStar_Tactics_Basic.recover)
                                              FStar_Syntax_Embeddings.e_any
                                              uu____1087 uu____1092
                                              (fun uu____1128  ->
                                                 FStar_Tactics_Basic.recover)
                                              FStar_TypeChecker_NBETerm.e_any
                                              uu____1099 uu____1104
                                             in
                                          let uu____1129 =
                                            let uu____1132 =
                                              FStar_Tactics_InterpFuns.mktac1
                                                Prims.int_zero "intro"
                                                FStar_Tactics_Basic.intro
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Reflection_Embeddings.e_binder
                                                FStar_Tactics_Basic.intro
                                                FStar_TypeChecker_NBETerm.e_unit
                                                FStar_Reflection_NBEEmbeddings.e_binder
                                               in
                                            let uu____1135 =
                                              let uu____1138 =
                                                let uu____1139 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Reflection_Embeddings.e_binder
                                                    FStar_Reflection_Embeddings.e_binder
                                                   in
                                                let uu____1146 =
                                                  FStar_TypeChecker_NBETerm.e_tuple2
                                                    FStar_Reflection_NBEEmbeddings.e_binder
                                                    FStar_Reflection_NBEEmbeddings.e_binder
                                                   in
                                                FStar_Tactics_InterpFuns.mktac1
                                                  Prims.int_zero "intro_rec"
                                                  FStar_Tactics_Basic.intro_rec
                                                  FStar_Syntax_Embeddings.e_unit
                                                  uu____1139
                                                  FStar_Tactics_Basic.intro_rec
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                  uu____1146
                                                 in
                                              let uu____1163 =
                                                let uu____1166 =
                                                  let uu____1167 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step
                                                     in
                                                  let uu____1172 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step
                                                     in
                                                  FStar_Tactics_InterpFuns.mktac1
                                                    Prims.int_zero "norm"
                                                    FStar_Tactics_Basic.norm
                                                    uu____1167
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Tactics_Basic.norm
                                                    uu____1172
                                                    FStar_TypeChecker_NBETerm.e_unit
                                                   in
                                                let uu____1183 =
                                                  let uu____1186 =
                                                    let uu____1187 =
                                                      FStar_Syntax_Embeddings.e_list
                                                        FStar_Syntax_Embeddings.e_norm_step
                                                       in
                                                    let uu____1192 =
                                                      FStar_TypeChecker_NBETerm.e_list
                                                        FStar_TypeChecker_NBETerm.e_norm_step
                                                       in
                                                    FStar_Tactics_InterpFuns.mktac3
                                                      Prims.int_zero
                                                      "norm_term_env"
                                                      FStar_Tactics_Basic.norm_term_env
                                                      FStar_Reflection_Embeddings.e_env
                                                      uu____1187
                                                      FStar_Reflection_Embeddings.e_term
                                                      FStar_Reflection_Embeddings.e_term
                                                      FStar_Tactics_Basic.norm_term_env
                                                      FStar_Reflection_NBEEmbeddings.e_env
                                                      uu____1192
                                                      FStar_Reflection_NBEEmbeddings.e_term
                                                      FStar_Reflection_NBEEmbeddings.e_term
                                                     in
                                                  let uu____1203 =
                                                    let uu____1206 =
                                                      let uu____1207 =
                                                        FStar_Syntax_Embeddings.e_list
                                                          FStar_Syntax_Embeddings.e_norm_step
                                                         in
                                                      let uu____1212 =
                                                        FStar_TypeChecker_NBETerm.e_list
                                                          FStar_TypeChecker_NBETerm.e_norm_step
                                                         in
                                                      FStar_Tactics_InterpFuns.mktac2
                                                        Prims.int_zero
                                                        "norm_binder_type"
                                                        FStar_Tactics_Basic.norm_binder_type
                                                        uu____1207
                                                        FStar_Reflection_Embeddings.e_binder
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_Basic.norm_binder_type
                                                        uu____1212
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                       in
                                                    let uu____1223 =
                                                      let uu____1226 =
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
                                                      let uu____1231 =
                                                        let uu____1234 =
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
                                                        let uu____1237 =
                                                          let uu____1240 =
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
                                                          let uu____1243 =
                                                            let uu____1246 =
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
                                                            let uu____1249 =
                                                              let uu____1252
                                                                =
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
                                                              let uu____1255
                                                                =
                                                                let uu____1258
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
                                                                let uu____1261
                                                                  =
                                                                  let uu____1264
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
                                                                  let uu____1267
                                                                    =
                                                                    let uu____1270
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
                                                                    let uu____1277
                                                                    =
                                                                    let uu____1280
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_one
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
                                                                    let uu____1287
                                                                    =
                                                                    let uu____1290
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
                                                                    let uu____1293
                                                                    =
                                                                    let uu____1296
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
                                                                    let uu____1301
                                                                    =
                                                                    let uu____1304
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "tcc"
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_comp
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_comp
                                                                     in
                                                                    let uu____1307
                                                                    =
                                                                    let uu____1310
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "tc"
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1313
                                                                    =
                                                                    let uu____1316
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
                                                                    let uu____1319
                                                                    =
                                                                    let uu____1322
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1327
                                                                     ->
                                                                    fun
                                                                    uu____1328
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1332
                                                                    =
                                                                    let uu____1335
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
                                                                    let uu____1340
                                                                    =
                                                                    let uu____1343
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
                                                                    let uu____1348
                                                                    =
                                                                    let uu____1351
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
                                                                    let uu____1356
                                                                    =
                                                                    let uu____1359
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
                                                                    let uu____1364
                                                                    =
                                                                    let uu____1367
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
                                                                    let uu____1372
                                                                    =
                                                                    let uu____1375
                                                                    =
                                                                    let uu____1376
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1381
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "t_pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1376
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1381
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1392
                                                                    =
                                                                    let uu____1395
                                                                    =
                                                                    let uu____1396
                                                                    =
                                                                    let uu____1409
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1409
                                                                     in
                                                                    let uu____1423
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1428
                                                                    =
                                                                    let uu____1441
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1441
                                                                     in
                                                                    let uu____1455
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1396
                                                                    uu____1423
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1428
                                                                    uu____1455
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1486
                                                                    =
                                                                    let uu____1489
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
                                                                    let uu____1492
                                                                    =
                                                                    let uu____1495
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
                                                                    let uu____1498
                                                                    =
                                                                    let uu____1501
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
                                                                    let uu____1504
                                                                    =
                                                                    let uu____1507
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
                                                                    let uu____1510
                                                                    =
                                                                    let uu____1513
                                                                    =
                                                                    let uu____1514
                                                                    =
                                                                    let uu____1523
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1523
                                                                     in
                                                                    let uu____1534
                                                                    =
                                                                    let uu____1543
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1543
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1514
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1534
                                                                     in
                                                                    let uu____1568
                                                                    =
                                                                    let uu____1571
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
                                                                    let uu____1574
                                                                    =
                                                                    let uu____1577
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
                                                                    let uu____1580
                                                                    =
                                                                    let uu____1583
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
                                                                    let uu____1586
                                                                    =
                                                                    let uu____1589
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
                                                                    let uu____1592
                                                                    =
                                                                    let uu____1595
                                                                    =
                                                                    let uu____1596
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1601
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1596
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1601
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1612
                                                                    =
                                                                    let uu____1615
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
                                                                    let uu____1620
                                                                    =
                                                                    let uu____1623
                                                                    =
                                                                    let uu____1624
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1631
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1624
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1631
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1652
                                                                    =
                                                                    let uu____1655
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
                                                                    let uu____1660
                                                                    =
                                                                    let uu____1663
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
                                                                    let uu____1666
                                                                    =
                                                                    let uu____1669
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
                                                                    let uu____1672
                                                                    =
                                                                    let uu____1675
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
                                                                    let uu____1678
                                                                    =
                                                                    let uu____1681
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
                                                                    let uu____1686
                                                                    =
                                                                    let uu____1689
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1696
                                                                     ->
                                                                    fun
                                                                    uu____1697
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1700
                                                                    =
                                                                    let uu____1703
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
                                                                    uu____1711
                                                                     ->
                                                                    fun
                                                                    uu____1712
                                                                     ->
                                                                    fun
                                                                    uu____1713
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____1703]
                                                                     in
                                                                    uu____1689
                                                                    ::
                                                                    uu____1700
                                                                     in
                                                                    uu____1681
                                                                    ::
                                                                    uu____1686
                                                                     in
                                                                    uu____1675
                                                                    ::
                                                                    uu____1678
                                                                     in
                                                                    uu____1669
                                                                    ::
                                                                    uu____1672
                                                                     in
                                                                    uu____1663
                                                                    ::
                                                                    uu____1666
                                                                     in
                                                                    uu____1655
                                                                    ::
                                                                    uu____1660
                                                                     in
                                                                    uu____1623
                                                                    ::
                                                                    uu____1652
                                                                     in
                                                                    uu____1615
                                                                    ::
                                                                    uu____1620
                                                                     in
                                                                    uu____1595
                                                                    ::
                                                                    uu____1612
                                                                     in
                                                                    uu____1589
                                                                    ::
                                                                    uu____1592
                                                                     in
                                                                    uu____1583
                                                                    ::
                                                                    uu____1586
                                                                     in
                                                                    uu____1577
                                                                    ::
                                                                    uu____1580
                                                                     in
                                                                    uu____1571
                                                                    ::
                                                                    uu____1574
                                                                     in
                                                                    uu____1513
                                                                    ::
                                                                    uu____1568
                                                                     in
                                                                    uu____1507
                                                                    ::
                                                                    uu____1510
                                                                     in
                                                                    uu____1501
                                                                    ::
                                                                    uu____1504
                                                                     in
                                                                    uu____1495
                                                                    ::
                                                                    uu____1498
                                                                     in
                                                                    uu____1489
                                                                    ::
                                                                    uu____1492
                                                                     in
                                                                    uu____1395
                                                                    ::
                                                                    uu____1486
                                                                     in
                                                                    uu____1375
                                                                    ::
                                                                    uu____1392
                                                                     in
                                                                    uu____1367
                                                                    ::
                                                                    uu____1372
                                                                     in
                                                                    uu____1359
                                                                    ::
                                                                    uu____1364
                                                                     in
                                                                    uu____1351
                                                                    ::
                                                                    uu____1356
                                                                     in
                                                                    uu____1343
                                                                    ::
                                                                    uu____1348
                                                                     in
                                                                    uu____1335
                                                                    ::
                                                                    uu____1340
                                                                     in
                                                                    uu____1322
                                                                    ::
                                                                    uu____1332
                                                                     in
                                                                    uu____1316
                                                                    ::
                                                                    uu____1319
                                                                     in
                                                                    uu____1310
                                                                    ::
                                                                    uu____1313
                                                                     in
                                                                    uu____1304
                                                                    ::
                                                                    uu____1307
                                                                     in
                                                                    uu____1296
                                                                    ::
                                                                    uu____1301
                                                                     in
                                                                    uu____1290
                                                                    ::
                                                                    uu____1293
                                                                     in
                                                                    uu____1280
                                                                    ::
                                                                    uu____1287
                                                                     in
                                                                    uu____1270
                                                                    ::
                                                                    uu____1277
                                                                     in
                                                                  uu____1264
                                                                    ::
                                                                    uu____1267
                                                                   in
                                                                uu____1258 ::
                                                                  uu____1261
                                                                 in
                                                              uu____1252 ::
                                                                uu____1255
                                                               in
                                                            uu____1246 ::
                                                              uu____1249
                                                             in
                                                          uu____1240 ::
                                                            uu____1243
                                                           in
                                                        uu____1234 ::
                                                          uu____1237
                                                         in
                                                      uu____1226 ::
                                                        uu____1231
                                                       in
                                                    uu____1206 :: uu____1223
                                                     in
                                                  uu____1186 :: uu____1203
                                                   in
                                                uu____1166 :: uu____1183  in
                                              uu____1138 :: uu____1163  in
                                            uu____1132 :: uu____1135  in
                                          uu____1086 :: uu____1129  in
                                        uu____1040 :: uu____1083  in
                                      uu____1034 :: uu____1037  in
                                    uu____1014 :: uu____1031  in
                                  uu____994 :: uu____1011  in
                                uu____932 :: uu____991  in
                              uu____924 :: uu____929  in
                            uu____916 :: uu____921  in
                          uu____908 :: uu____913  in
                        uu____902 :: uu____905  in
                      uu____896 :: uu____899  in
                    uu____890 :: uu____893  in
                  uu____870 :: uu____887  in
                uu____850 :: uu____867  in
              uu____844 :: uu____847  in
            uu____838 :: uu____841  in
          uu____832 :: uu____835  in
        uu____826 :: uu____829  in
      uu____820 :: uu____823  in
    let uu____1716 = FStar_Tactics_InterpFuns.native_tactics_steps ()  in
    FStar_List.append uu____817 uu____1716

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
              let uu____1734 =
                let uu____1739 =
                  let uu____1740 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____1740]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____1739  in
              uu____1734 FStar_Pervasives_Native.None rng  in
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
               let uu____1790 =
                 let uu____1795 =
                   let uu____1796 =
                     let uu____1805 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1805  in
                   [uu____1796]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1795  in
               uu____1790 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1846 = FStar_Options.tactics_nbe ()  in
               if uu____1846
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             let result =
               let uu____1868 = primitive_steps ()  in
               norm_f uu____1868 steps
                 proof_state.FStar_Tactics_Types.main_context tm
                in
             let res =
               let uu____1876 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Tactics_InterpFuns.unembed uu____1876 result ncb  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1889 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1889
                   (fun uu____1893  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1898 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1898
                   (fun uu____1902  -> FStar_Tactics_Basic.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____1905 =
                   let uu____1911 =
                     let uu____1913 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1913
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1911)  in
                 FStar_Errors.raise_error uu____1905
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
              let uu____1930 =
                let uu____1931 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____1931]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1930  in
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
               let uu____1957 =
                 let uu____1958 =
                   let uu____1963 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1963  in
                 [uu____1958]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1957
                in
             let res =
               let uu____1977 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1977 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1990 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1990
                   (fun uu____1994  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1999 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1999
                   (fun uu____2003  -> FStar_Tactics_Basic.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____2006 =
                   let uu____2012 =
                     let uu____2014 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2014
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2012)  in
                 FStar_Errors.raise_error uu____2006
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
                 let uu____2044 =
                   let uu____2049 =
                     let uu____2050 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____2050]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____2049  in
                 uu____2044 FStar_Pervasives_Native.None rng  in
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
      let em uu____2107 uu____2108 uu____2109 uu____2110 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n1 =
        let uu____2159 = unembed_tactic_1_alt ea er t0 n1  in
        match uu____2159 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____2199 = f x  in FStar_Tactics_Basic.run uu____2199))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____2215 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____2215

let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____2255 =
               let uu____2257 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____2259 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2257 uu____2259 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2255, rng)) is
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
            (let uu____2303 = FStar_ST.op_Bang tacdbg  in
             if uu____2303
             then
               let uu____2327 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____2327
             else ());
            (let uu____2332 = FStar_TypeChecker_TcTerm.tc_tactic env tactic
                in
             match uu____2332 with
             | (uu____2345,uu____2346,g) ->
                 ((let uu____2349 = FStar_ST.op_Bang tacdbg  in
                   if uu____2349 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_1 FStar_Syntax_Embeddings.e_unit
                       FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb
                      in
                   let uu____2385 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____2385 with
                   | (env1,uu____2399) ->
                       let env2 =
                         let uu___199_2405 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___199_2405.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___199_2405.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___199_2405.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___199_2405.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___199_2405.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___199_2405.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___199_2405.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___199_2405.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___199_2405.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___199_2405.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___199_2405.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___199_2405.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___199_2405.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___199_2405.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___199_2405.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___199_2405.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___199_2405.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___199_2405.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___199_2405.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___199_2405.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___199_2405.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___199_2405.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___199_2405.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___199_2405.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___199_2405.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___199_2405.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___199_2405.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___199_2405.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___199_2405.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___199_2405.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___199_2405.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___199_2405.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___199_2405.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___199_2405.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___199_2405.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___199_2405.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___199_2405.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___199_2405.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___199_2405.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___199_2405.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___199_2405.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___199_2405.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___199_2405.FStar_TypeChecker_Env.strict_args_tab)
                         }  in
                       let env3 =
                         let uu___202_2408 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___202_2408.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___202_2408.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___202_2408.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___202_2408.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___202_2408.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___202_2408.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___202_2408.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___202_2408.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___202_2408.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___202_2408.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___202_2408.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___202_2408.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___202_2408.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___202_2408.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___202_2408.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___202_2408.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___202_2408.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___202_2408.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___202_2408.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___202_2408.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___202_2408.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___202_2408.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___202_2408.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___202_2408.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___202_2408.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___202_2408.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___202_2408.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___202_2408.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___202_2408.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___202_2408.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___202_2408.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___202_2408.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___202_2408.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___202_2408.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___202_2408.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___202_2408.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___202_2408.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___202_2408.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___202_2408.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___202_2408.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___202_2408.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___202_2408.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___202_2408.FStar_TypeChecker_Env.strict_args_tab)
                         }  in
                       let env4 =
                         let uu___205_2411 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_2411.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_2411.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_2411.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_2411.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___205_2411.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_2411.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_2411.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___205_2411.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_2411.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___205_2411.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_2411.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_2411.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_2411.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_2411.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_2411.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_2411.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_2411.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_2411.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_2411.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_2411.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___205_2411.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_2411.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___205_2411.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___205_2411.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___205_2411.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___205_2411.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_2411.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_2411.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___205_2411.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___205_2411.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___205_2411.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___205_2411.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___205_2411.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_2411.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___205_2411.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___205_2411.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___205_2411.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___205_2411.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___205_2411.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___205_2411.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___205_2411.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___205_2411.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___205_2411.FStar_TypeChecker_Env.strict_args_tab)
                         }  in
                       let rng =
                         let uu____2414 = FStar_Range.use_range rng_goal  in
                         let uu____2415 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____2414 uu____2415  in
                       let uu____2416 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____2416 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____2454 = FStar_ST.op_Bang tacdbg  in
                              if uu____2454
                              then
                                let uu____2478 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____2478
                              else ());
                             (let uu____2483 =
                                FStar_Util.record_time
                                  (fun uu____2495  ->
                                     let uu____2496 = tau ()  in
                                     FStar_Tactics_Basic.run_safe uu____2496
                                       ps)
                                 in
                              match uu____2483 with
                              | (res,ms) ->
                                  ((let uu____2514 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____2514
                                    then FStar_Util.print_string "}\n"
                                    else ());
                                   (let uu____2542 =
                                      (FStar_ST.op_Bang tacdbg) ||
                                        (FStar_Options.tactics_info ())
                                       in
                                    if uu____2542
                                    then
                                      let uu____2566 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____2568 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____2570 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "Tactic %s ran in %s ms (%s)\n"
                                        uu____2566 uu____2568 uu____2570
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____2581,ps1) ->
                                        ((let uu____2584 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2584
                                          then
                                            let uu____2608 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____2608
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____2618 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____2618
                                              then
                                                let uu____2621 =
                                                  let uu____2623 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____2624 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt_force
                                                    uu____2623 uu____2624
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____2621
                                                 then ()
                                                 else
                                                   (let uu____2628 =
                                                      let uu____2630 =
                                                        let uu____2632 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____2632
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____2630
                                                       in
                                                    failwith uu____2628))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____2637 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2637
                                          then
                                            let uu____2661 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____2661
                                          else ());
                                         (let g1 =
                                            let uu___236_2669 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___236_2669.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___236_2669.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___236_2669.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____2672 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____2672
                                           then
                                             let uu____2696 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits)
                                                in
                                             let uu____2698 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____2696 uu____2698
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____2707 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2707
                                            then
                                              let uu____2731 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits)
                                                 in
                                              let uu____2733 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____2731 uu____2733
                                            else ());
                                           report_implicits rng_goal
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____2742 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2742
                                            then
                                              let uu____2766 =
                                                let uu____2767 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc
                                                   in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____2767 ps1
                                                 in
                                              FStar_Tactics_Basic.do_dump_proofstate
                                                uu____2766
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (e,ps1) ->
                                        ((let uu____2776 =
                                            let uu____2777 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____2777 ps1
                                             in
                                          FStar_Tactics_Basic.do_dump_proofstate
                                            uu____2776
                                            "at the time of failure");
                                         (let texn_to_string e1 =
                                            match e1 with
                                            | FStar_Tactics_Types.TacticFailure
                                                s -> s
                                            | FStar_Tactics_Types.EExn t ->
                                                let uu____2790 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                Prims.op_Hat
                                                  "uncaught exception: "
                                                  uu____2790
                                            | e2 -> FStar_Exn.raise e2  in
                                          let uu____2795 =
                                            let uu____2801 =
                                              let uu____2803 =
                                                texn_to_string e  in
                                              FStar_Util.format1
                                                "user tactic failed: %s"
                                                uu____2803
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____2801)
                                             in
                                          FStar_Errors.raise_error uu____2795
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2822 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2833 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2844 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2903 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2947 -> false
  
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3005 -> false
  
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____3048 . 'Auu____3048 -> 'Auu____3048 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3078 = FStar_Syntax_Util.head_and_args t  in
        match uu____3078 with
        | (hd1,args) ->
            let uu____3121 =
              let uu____3136 =
                let uu____3137 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3137.FStar_Syntax_Syntax.n  in
              (uu____3136, args)  in
            (match uu____3121 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(tactic,FStar_Pervasives_Native.None )::(assertion,FStar_Pervasives_Native.None
                                                            )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3199 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3199 with
                       | (gs,uu____3207) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3214 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3214 with
                       | (gs,uu____3222) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3265 =
                        let uu____3272 =
                          let uu____3275 =
                            let uu____3276 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3276
                             in
                          [uu____3275]  in
                        (FStar_Syntax_Util.t_true, uu____3272)  in
                      Simplified uu____3265
                  | Both  ->
                      let uu____3287 =
                        let uu____3296 =
                          let uu____3299 =
                            let uu____3300 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3300
                             in
                          [uu____3299]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3296)  in
                      Dual uu____3287
                  | Neg  -> Simplified (assertion, []))
             | uu____3313 -> Unchanged t)
  
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___0_3405  ->
      match uu___0_3405 with
      | Unchanged t -> let uu____3411 = f t  in Unchanged uu____3411
      | Simplified (t,gs) ->
          let uu____3418 = let uu____3425 = f t  in (uu____3425, gs)  in
          Simplified uu____3418
      | Dual (tn,tp,gs) ->
          let uu____3435 =
            let uu____3444 = f tn  in
            let uu____3445 = f tp  in (uu____3444, uu____3445, gs)  in
          Dual uu____3435
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3509 = f t1 t2  in Unchanged uu____3509
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3521 = let uu____3528 = f t1 t2  in (uu____3528, gs)
               in
            Simplified uu____3521
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3542 = let uu____3549 = f t1 t2  in (uu____3549, gs)
               in
            Simplified uu____3542
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3568 =
              let uu____3575 = f t1 t2  in
              (uu____3575, (FStar_List.append gs1 gs2))  in
            Simplified uu____3568
        | uu____3578 ->
            let uu____3587 = explode x  in
            (match uu____3587 with
             | (n1,p1,gs1) ->
                 let uu____3605 = explode y  in
                 (match uu____3605 with
                  | (n2,p2,gs2) ->
                      let uu____3623 =
                        let uu____3632 = f n1 n2  in
                        let uu____3633 = f p1 p2  in
                        (uu____3632, uu____3633, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3623))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3706 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3706
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3755  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3798 =
              let uu____3799 = FStar_Syntax_Subst.compress t  in
              uu____3799.FStar_Syntax_Syntax.n  in
            match uu____3798 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3811 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3811 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3837 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3837 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3857;
                   FStar_Syntax_Syntax.vars = uu____3858;_},(p,uu____3860)::
                 (q,uu____3862)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3920 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3920 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3934 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3934.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3938;
                   FStar_Syntax_Syntax.vars = uu____3939;_},(p,uu____3941)::
                 (q,uu____3943)::[])
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
                  let uu____4001 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4001 p  in
                let r2 =
                  let uu____4003 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4003 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4010,Unchanged uu____4011) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4029 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4029.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4032 ->
                     let uu____4041 = explode r1  in
                     (match uu____4041 with
                      | (pn,pp,gs1) ->
                          let uu____4059 = explode r2  in
                          (match uu____4059 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4080 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4083 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4080
                                   uu____4083
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4147  ->
                       fun r  ->
                         match uu____4147 with
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
                let uu____4299 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4299 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4339  ->
                            match uu____4339 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4361 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___494_4393 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___494_4393.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___494_4393.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4361 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4421 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4421.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4467 = traverse f pol e t1  in
                let uu____4472 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4472 uu____4467
            | FStar_Syntax_Syntax.Tm_match (sc,brs) ->
                let uu____4547 = traverse f pol e sc  in
                let uu____4552 =
                  let uu____4571 =
                    FStar_List.map
                      (fun br  ->
                         let uu____4588 = FStar_Syntax_Subst.open_branch br
                            in
                         match uu____4588 with
                         | (pat,w,exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs
                                in
                             let r = traverse f pol e1 exp  in
                             let uu____4615 =
                               comb1
                                 (fun exp1  ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1))
                                in
                             uu____4615 r) brs
                     in
                  comb_list uu____4571  in
                comb2
                  (fun sc1  ->
                     fun brs1  -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____4547 uu____4552
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___526_4701 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___526_4701.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___526_4701.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4708 =
                f pol e
                  (let uu___532_4712 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___532_4712.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___532_4712.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4708
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___539_4722 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___539_4722.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___539_4722.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4723 = explode rp  in
              (match uu____4723 with
               | (uu____4732,p',gs') ->
                   Dual
                     ((let uu___546_4742 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___546_4742.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___546_4742.FStar_Syntax_Syntax.vars)
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
      (let uu____4787 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4787);
      (let uu____4812 = FStar_ST.op_Bang tacdbg  in
       if uu____4812
       then
         let uu____4836 =
           let uu____4838 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4838
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4841 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4836
           uu____4841
       else ());
      (let initial = (Prims.int_one, [])  in
       let uu____4876 =
         let uu____4885 = traverse by_tactic_interp Pos env goal  in
         match uu____4885 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4909 -> failwith "no"  in
       match uu____4876 with
       | (t',gs) ->
           ((let uu____4938 = FStar_ST.op_Bang tacdbg  in
             if uu____4938
             then
               let uu____4962 =
                 let uu____4964 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4964
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4967 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4962 uu____4967
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5022  ->
                    fun g  ->
                      match uu____5022 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____5071 =
                              let uu____5074 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____5075 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____5074 uu____5075  in
                            match uu____5071 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5076 =
                                  let uu____5082 =
                                    let uu____5084 =
                                      let uu____5086 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____5086
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5084
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5082)
                                   in
                                FStar_Errors.raise_error uu____5076
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5091 = FStar_ST.op_Bang tacdbg  in
                            if uu____5091
                            then
                              let uu____5115 = FStar_Util.string_of_int n1
                                 in
                              let uu____5117 =
                                let uu____5119 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____5119
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5115 uu____5117
                            else ());
                           (let label1 =
                              let uu____5125 =
                                let uu____5127 =
                                  FStar_Tactics_Types.get_label g  in
                                uu____5127 = ""  in
                              if uu____5125
                              then
                                let uu____5133 = FStar_Util.string_of_int n1
                                   in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____5133
                              else
                                (let uu____5138 =
                                   let uu____5140 =
                                     FStar_Util.string_of_int n1  in
                                   let uu____5142 =
                                     let uu____5144 =
                                       let uu____5146 =
                                         FStar_Tactics_Types.get_label g  in
                                       Prims.op_Hat uu____5146 ")"  in
                                     Prims.op_Hat " (" uu____5144  in
                                   Prims.op_Hat uu____5140 uu____5142  in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____5138)
                               in
                            let gt' =
                              FStar_TypeChecker_Util.label label1
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____5152 =
                              let uu____5161 =
                                let uu____5168 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____5168, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____5161 :: gs1  in
                            ((n1 + Prims.int_one), uu____5152)))) s gs
                in
             let uu____5185 = s1  in
             match uu____5185 with
             | (uu____5207,gs1) ->
                 let uu____5227 =
                   let uu____5234 = FStar_Options.peek ()  in
                   (env, t', uu____5234)  in
                 uu____5227 :: gs1)))
  
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
          let uu____5258 =
            let uu____5263 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____5264 =
              let uu____5265 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5265]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____5263 uu____5264  in
          uu____5258 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____5293 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5293);
           (let uu____5317 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____5317 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____5338 =
                        let uu____5341 = FStar_Tactics_Types.goal_env g  in
                        let uu____5342 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____5341 uu____5342  in
                      match uu____5338 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____5345 = FStar_ST.op_Bang tacdbg  in
                            if uu____5345
                            then
                              let uu____5369 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____5369
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____5384 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____5384 guard))
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
        ((let uu____5406 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____5406);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____5431 =
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos tau env typ
             in
          match uu____5431 with
          | (gs,w) ->
              ((let uu____5447 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____5452 =
                         let uu____5454 =
                           let uu____5457 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____5458 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____5457 uu____5458  in
                         FStar_Option.isSome uu____5454  in
                       Prims.op_Negation uu____5452) gs
                   in
                if uu____5447
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
                (let uu____5466 = FStar_ST.op_Bang tacdbg  in
                 if uu____5466
                 then
                   let uu____5490 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____5490
                 else ());
                (let uu____5495 =
                   let uu____5500 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____5500 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____5495 with
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
            ((let uu____5545 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")
                 in
              FStar_ST.op_Colon_Equals tacdbg uu____5545);
             (let uu____5569 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None
                 in
              match uu____5569 with
              | (uvtm,uu____5588,g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ  in
                  let goal =
                    let uu____5606 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm
                       in
                    FStar_Syntax_Util.mk_squash u uu____5606  in
                  let uu____5607 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal
                     in
                  (match uu____5607 with
                   | (gs,w) ->
                       (FStar_List.iter
                          (fun g  ->
                             let uu____5628 =
                               let uu____5631 =
                                 FStar_Tactics_Types.goal_env g  in
                               let uu____5632 =
                                 FStar_Tactics_Types.goal_type g  in
                               getprop uu____5631 uu____5632  in
                             match uu____5628 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____5635 = FStar_ST.op_Bang tacdbg
                                      in
                                   if uu____5635
                                   then
                                     let uu____5659 =
                                       FStar_Syntax_Print.term_to_string vc
                                        in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____5659
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
                                   let uu____5674 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____5674 guard))
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
  