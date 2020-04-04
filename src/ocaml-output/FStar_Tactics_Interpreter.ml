open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____12  ->
    let step_from_native_step s =
      {
        FStar_TypeChecker_Cfg.name = (s.FStar_Tactics_Native.name);
        FStar_TypeChecker_Cfg.arity = (s.FStar_Tactics_Native.arity);
        FStar_TypeChecker_Cfg.univ_arity = Prims.int_zero;
        FStar_TypeChecker_Cfg.auto_reflect =
          (FStar_Pervasives_Native.Some
             (s.FStar_Tactics_Native.arity - Prims.int_one));
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (s.FStar_Tactics_Native.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution = false;
        FStar_TypeChecker_Cfg.interpretation =
          (s.FStar_Tactics_Native.tactic);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (fun _cb  ->
             FStar_TypeChecker_NBETerm.dummy_interp
               s.FStar_Tactics_Native.name)
      }  in
    let uu____25 = FStar_Tactics_Native.list_all ()  in
    FStar_List.map step_from_native_step uu____25
  
let mktot1' :
  'Auu____53 'Auu____54 'Auu____55 'Auu____56 .
    Prims.int ->
      Prims.string ->
        ('Auu____53 -> 'Auu____54) ->
          'Auu____53 FStar_Syntax_Embeddings.embedding ->
            'Auu____54 FStar_Syntax_Embeddings.embedding ->
              ('Auu____55 -> 'Auu____56) ->
                'Auu____55 FStar_TypeChecker_NBETerm.embedding ->
                  'Auu____56 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___13_127 =
                    FStar_Tactics_InterpFuns.mktot1 uarity nm f ea er nf ena
                      enr
                     in
                  let uu____128 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____128;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___13_127.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___13_127.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___13_127.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___13_127.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___13_127.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___13_127.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___13_127.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot1'_psc :
  'Auu____155 'Auu____156 'Auu____157 'Auu____158 .
    Prims.int ->
      Prims.string ->
        (FStar_TypeChecker_Cfg.psc -> 'Auu____155 -> 'Auu____156) ->
          'Auu____155 FStar_Syntax_Embeddings.embedding ->
            'Auu____156 FStar_Syntax_Embeddings.embedding ->
              (FStar_TypeChecker_Cfg.psc -> 'Auu____157 -> 'Auu____158) ->
                'Auu____157 FStar_TypeChecker_NBETerm.embedding ->
                  'Auu____158 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___23_239 =
                    FStar_Tactics_InterpFuns.mktot1_psc uarity nm f ea er nf
                      ena enr
                     in
                  let uu____240 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____240;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___23_239.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___23_239.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___23_239.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___23_239.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___23_239.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___23_239.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___23_239.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot2' :
  'Auu____275 'Auu____276 'Auu____277 'Auu____278 'Auu____279 'Auu____280 .
    Prims.int ->
      Prims.string ->
        ('Auu____275 -> 'Auu____276 -> 'Auu____277) ->
          'Auu____275 FStar_Syntax_Embeddings.embedding ->
            'Auu____276 FStar_Syntax_Embeddings.embedding ->
              'Auu____277 FStar_Syntax_Embeddings.embedding ->
                ('Auu____278 -> 'Auu____279 -> 'Auu____280) ->
                  'Auu____278 FStar_TypeChecker_NBETerm.embedding ->
                    'Auu____279 FStar_TypeChecker_NBETerm.embedding ->
                      'Auu____280 FStar_TypeChecker_NBETerm.embedding ->
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
                      let uu___35_379 =
                        FStar_Tactics_InterpFuns.mktot2 uarity nm f ea eb er
                          nf ena enb enr
                         in
                      let uu____380 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm)
                         in
                      {
                        FStar_TypeChecker_Cfg.name = uu____380;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___35_379.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___35_379.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___35_379.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___35_379.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___35_379.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___35_379.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___35_379.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
  
let rec e_tactic_thunk :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Monad.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____612 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____619  ->
         fun uu____620  ->
           fun uu____621  ->
             fun uu____622  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____636 =
               let uu____639 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____639 ()  in
             FStar_Pervasives_Native.Some uu____636) uu____612

and e_tactic_nbe_thunk :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Monad.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____651 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____657  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____666 =
             let uu____669 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____669 ()  in
           FStar_Pervasives_Native.Some uu____666)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____651

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Monad.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____684 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____694  ->
           fun uu____695  ->
             fun uu____696  ->
               fun uu____697  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____713 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____713) uu____684

and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Monad.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____731 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____740  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____751 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____751)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____731

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____763  ->
    let uu____766 =
      let uu____769 =
        mktot1'_psc Prims.int_zero "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____772 =
        let uu____775 =
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
        let uu____778 =
          let uu____781 =
            mktot1' Prims.int_zero "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe
             in
          let uu____784 =
            let uu____787 =
              mktot1' Prims.int_zero "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____790 =
              let uu____793 =
                let uu____794 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal
                   in
                let uu____799 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe
                   in
                mktot1' Prims.int_zero "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____794
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____799
                 in
              let uu____810 =
                let uu____813 =
                  let uu____814 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____819 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mktot1' Prims.int_zero "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____814
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____819
                   in
                let uu____830 =
                  let uu____833 =
                    mktot1' Prims.int_zero "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env
                     in
                  let uu____836 =
                    let uu____839 =
                      mktot1' Prims.int_zero "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term
                       in
                    let uu____842 =
                      let uu____845 =
                        mktot1' Prims.int_zero "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____848 =
                        let uu____851 =
                          mktot1' Prims.int_zero "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool
                           in
                        let uu____856 =
                          let uu____859 =
                            mktot1' Prims.int_zero "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string
                             in
                          let uu____864 =
                            let uu____867 =
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
                            let uu____872 =
                              let uu____875 =
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
                              let uu____934 =
                                let uu____937 =
                                  let uu____938 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal
                                     in
                                  let uu____943 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe
                                     in
                                  FStar_Tactics_InterpFuns.mktac1
                                    Prims.int_zero "set_goals"
                                    FStar_Tactics_Monad.set_goals uu____938
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Monad.set_goals uu____943
                                    FStar_TypeChecker_NBETerm.e_unit
                                   in
                                let uu____954 =
                                  let uu____957 =
                                    let uu____958 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Tactics_Embedding.e_goal
                                       in
                                    let uu____963 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Tactics_Embedding.e_goal_nbe
                                       in
                                    FStar_Tactics_InterpFuns.mktac1
                                      Prims.int_zero "set_smt_goals"
                                      FStar_Tactics_Monad.set_smt_goals
                                      uu____958
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Monad.set_smt_goals
                                      uu____963
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____974 =
                                    let uu____977 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        Prims.int_zero "trivial"
                                        FStar_Tactics_Basic.trivial
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.trivial
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____980 =
                                      let uu____983 =
                                        let uu____984 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____989 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____996 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        let uu____1001 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        FStar_Tactics_InterpFuns.mktac2
                                          Prims.int_one "catch"
                                          (fun uu____1023  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____984 uu____989
                                          (fun uu____1025  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____996 uu____1001
                                         in
                                      let uu____1026 =
                                        let uu____1029 =
                                          let uu____1030 =
                                            e_tactic_thunk
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____1035 =
                                            FStar_Syntax_Embeddings.e_either
                                              FStar_Tactics_Embedding.e_exn
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____1042 =
                                            e_tactic_nbe_thunk
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          let uu____1047 =
                                            FStar_TypeChecker_NBETerm.e_either
                                              FStar_Tactics_Embedding.e_exn_nbe
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          FStar_Tactics_InterpFuns.mktac2
                                            Prims.int_one "recover"
                                            (fun uu____1069  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_Syntax_Embeddings.e_any
                                            uu____1030 uu____1035
                                            (fun uu____1071  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_TypeChecker_NBETerm.e_any
                                            uu____1042 uu____1047
                                           in
                                        let uu____1072 =
                                          let uu____1075 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              Prims.int_zero "intro"
                                              FStar_Tactics_Basic.intro
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Tactics_Basic.intro
                                              FStar_TypeChecker_NBETerm.e_unit
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                             in
                                          let uu____1078 =
                                            let uu____1081 =
                                              let uu____1082 =
                                                FStar_Syntax_Embeddings.e_tuple2
                                                  FStar_Reflection_Embeddings.e_binder
                                                  FStar_Reflection_Embeddings.e_binder
                                                 in
                                              let uu____1089 =
                                                FStar_TypeChecker_NBETerm.e_tuple2
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                 in
                                              FStar_Tactics_InterpFuns.mktac1
                                                Prims.int_zero "intro_rec"
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_Syntax_Embeddings.e_unit
                                                uu____1082
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_TypeChecker_NBETerm.e_unit
                                                uu____1089
                                               in
                                            let uu____1106 =
                                              let uu____1109 =
                                                let uu____1110 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step
                                                   in
                                                let uu____1115 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step
                                                   in
                                                FStar_Tactics_InterpFuns.mktac1
                                                  Prims.int_zero "norm"
                                                  FStar_Tactics_Basic.norm
                                                  uu____1110
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.norm
                                                  uu____1115
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                 in
                                              let uu____1126 =
                                                let uu____1129 =
                                                  let uu____1130 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step
                                                     in
                                                  let uu____1135 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step
                                                     in
                                                  FStar_Tactics_InterpFuns.mktac3
                                                    Prims.int_zero
                                                    "norm_term_env"
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_Embeddings.e_env
                                                    uu____1130
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    uu____1135
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                   in
                                                let uu____1146 =
                                                  let uu____1149 =
                                                    let uu____1150 =
                                                      FStar_Syntax_Embeddings.e_list
                                                        FStar_Syntax_Embeddings.e_norm_step
                                                       in
                                                    let uu____1155 =
                                                      FStar_TypeChecker_NBETerm.e_list
                                                        FStar_TypeChecker_NBETerm.e_norm_step
                                                       in
                                                    FStar_Tactics_InterpFuns.mktac2
                                                      Prims.int_zero
                                                      "norm_binder_type"
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____1150
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Syntax_Embeddings.e_unit
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____1155
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                      FStar_TypeChecker_NBETerm.e_unit
                                                     in
                                                  let uu____1166 =
                                                    let uu____1169 =
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
                                                    let uu____1174 =
                                                      let uu____1177 =
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
                                                      let uu____1180 =
                                                        let uu____1183 =
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
                                                        let uu____1186 =
                                                          let uu____1189 =
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
                                                          let uu____1192 =
                                                            let uu____1195 =
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
                                                            let uu____1198 =
                                                              let uu____1201
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
                                                              let uu____1204
                                                                =
                                                                let uu____1207
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
                                                                let uu____1210
                                                                  =
                                                                  let uu____1213
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
                                                                  let uu____1220
                                                                    =
                                                                    let uu____1223
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
                                                                    let uu____1230
                                                                    =
                                                                    let uu____1233
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
                                                                    let uu____1236
                                                                    =
                                                                    let uu____1239
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
                                                                    let uu____1244
                                                                    =
                                                                    let uu____1247
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
                                                                    let uu____1250
                                                                    =
                                                                    let uu____1253
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
                                                                    let uu____1256
                                                                    =
                                                                    let uu____1259
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
                                                                    let uu____1262
                                                                    =
                                                                    let uu____1265
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1270
                                                                     ->
                                                                    fun
                                                                    uu____1271
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1275
                                                                    =
                                                                    let uu____1278
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
                                                                    let uu____1283
                                                                    =
                                                                    let uu____1286
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
                                                                    let uu____1291
                                                                    =
                                                                    let uu____1294
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
                                                                    let uu____1299
                                                                    =
                                                                    let uu____1302
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
                                                                    let uu____1307
                                                                    =
                                                                    let uu____1310
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
                                                                    let uu____1315
                                                                    =
                                                                    let uu____1318
                                                                    =
                                                                    let uu____1319
                                                                    =
                                                                    let uu____1332
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1332
                                                                     in
                                                                    let uu____1346
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1351
                                                                    =
                                                                    let uu____1364
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1364
                                                                     in
                                                                    let uu____1378
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1319
                                                                    uu____1346
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1351
                                                                    uu____1378
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1409
                                                                    =
                                                                    let uu____1412
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
                                                                    let uu____1415
                                                                    =
                                                                    let uu____1418
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
                                                                    let uu____1421
                                                                    =
                                                                    let uu____1424
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
                                                                    let uu____1427
                                                                    =
                                                                    let uu____1430
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
                                                                    let uu____1433
                                                                    =
                                                                    let uu____1436
                                                                    =
                                                                    let uu____1437
                                                                    =
                                                                    let uu____1446
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1446
                                                                     in
                                                                    let uu____1457
                                                                    =
                                                                    let uu____1466
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1466
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1437
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1457
                                                                     in
                                                                    let uu____1491
                                                                    =
                                                                    let uu____1494
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
                                                                    let uu____1497
                                                                    =
                                                                    let uu____1500
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
                                                                    let uu____1503
                                                                    =
                                                                    let uu____1506
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
                                                                    let uu____1509
                                                                    =
                                                                    let uu____1512
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
                                                                    let uu____1515
                                                                    =
                                                                    let uu____1518
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
                                                                    let uu____1521
                                                                    =
                                                                    let uu____1524
                                                                    =
                                                                    let uu____1525
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1530
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1525
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1530
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1541
                                                                    =
                                                                    let uu____1544
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
                                                                    let uu____1549
                                                                    =
                                                                    let uu____1552
                                                                    =
                                                                    let uu____1553
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1560
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1553
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1560
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1581
                                                                    =
                                                                    let uu____1584
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
                                                                    let uu____1589
                                                                    =
                                                                    let uu____1592
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
                                                                    let uu____1595
                                                                    =
                                                                    let uu____1598
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
                                                                    let uu____1601
                                                                    =
                                                                    let uu____1604
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
                                                                    let uu____1607
                                                                    =
                                                                    let uu____1610
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
                                                                    let uu____1615
                                                                    =
                                                                    let uu____1618
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1625
                                                                     ->
                                                                    fun
                                                                    uu____1626
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1629
                                                                    =
                                                                    let uu____1632
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
                                                                    uu____1640
                                                                     ->
                                                                    fun
                                                                    uu____1641
                                                                     ->
                                                                    fun
                                                                    uu____1642
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____1632]
                                                                     in
                                                                    uu____1618
                                                                    ::
                                                                    uu____1629
                                                                     in
                                                                    uu____1610
                                                                    ::
                                                                    uu____1615
                                                                     in
                                                                    uu____1604
                                                                    ::
                                                                    uu____1607
                                                                     in
                                                                    uu____1598
                                                                    ::
                                                                    uu____1601
                                                                     in
                                                                    uu____1592
                                                                    ::
                                                                    uu____1595
                                                                     in
                                                                    uu____1584
                                                                    ::
                                                                    uu____1589
                                                                     in
                                                                    uu____1552
                                                                    ::
                                                                    uu____1581
                                                                     in
                                                                    uu____1544
                                                                    ::
                                                                    uu____1549
                                                                     in
                                                                    uu____1524
                                                                    ::
                                                                    uu____1541
                                                                     in
                                                                    uu____1518
                                                                    ::
                                                                    uu____1521
                                                                     in
                                                                    uu____1512
                                                                    ::
                                                                    uu____1515
                                                                     in
                                                                    uu____1506
                                                                    ::
                                                                    uu____1509
                                                                     in
                                                                    uu____1500
                                                                    ::
                                                                    uu____1503
                                                                     in
                                                                    uu____1494
                                                                    ::
                                                                    uu____1497
                                                                     in
                                                                    uu____1436
                                                                    ::
                                                                    uu____1491
                                                                     in
                                                                    uu____1430
                                                                    ::
                                                                    uu____1433
                                                                     in
                                                                    uu____1424
                                                                    ::
                                                                    uu____1427
                                                                     in
                                                                    uu____1418
                                                                    ::
                                                                    uu____1421
                                                                     in
                                                                    uu____1412
                                                                    ::
                                                                    uu____1415
                                                                     in
                                                                    uu____1318
                                                                    ::
                                                                    uu____1409
                                                                     in
                                                                    uu____1310
                                                                    ::
                                                                    uu____1315
                                                                     in
                                                                    uu____1302
                                                                    ::
                                                                    uu____1307
                                                                     in
                                                                    uu____1294
                                                                    ::
                                                                    uu____1299
                                                                     in
                                                                    uu____1286
                                                                    ::
                                                                    uu____1291
                                                                     in
                                                                    uu____1278
                                                                    ::
                                                                    uu____1283
                                                                     in
                                                                    uu____1265
                                                                    ::
                                                                    uu____1275
                                                                     in
                                                                    uu____1259
                                                                    ::
                                                                    uu____1262
                                                                     in
                                                                    uu____1253
                                                                    ::
                                                                    uu____1256
                                                                     in
                                                                    uu____1247
                                                                    ::
                                                                    uu____1250
                                                                     in
                                                                    uu____1239
                                                                    ::
                                                                    uu____1244
                                                                     in
                                                                    uu____1233
                                                                    ::
                                                                    uu____1236
                                                                     in
                                                                    uu____1223
                                                                    ::
                                                                    uu____1230
                                                                     in
                                                                  uu____1213
                                                                    ::
                                                                    uu____1220
                                                                   in
                                                                uu____1207 ::
                                                                  uu____1210
                                                                 in
                                                              uu____1201 ::
                                                                uu____1204
                                                               in
                                                            uu____1195 ::
                                                              uu____1198
                                                             in
                                                          uu____1189 ::
                                                            uu____1192
                                                           in
                                                        uu____1183 ::
                                                          uu____1186
                                                         in
                                                      uu____1177 ::
                                                        uu____1180
                                                       in
                                                    uu____1169 :: uu____1174
                                                     in
                                                  uu____1149 :: uu____1166
                                                   in
                                                uu____1129 :: uu____1146  in
                                              uu____1109 :: uu____1126  in
                                            uu____1081 :: uu____1106  in
                                          uu____1075 :: uu____1078  in
                                        uu____1029 :: uu____1072  in
                                      uu____983 :: uu____1026  in
                                    uu____977 :: uu____980  in
                                  uu____957 :: uu____974  in
                                uu____937 :: uu____954  in
                              uu____875 :: uu____934  in
                            uu____867 :: uu____872  in
                          uu____859 :: uu____864  in
                        uu____851 :: uu____856  in
                      uu____845 :: uu____848  in
                    uu____839 :: uu____842  in
                  uu____833 :: uu____836  in
                uu____813 :: uu____830  in
              uu____793 :: uu____810  in
            uu____787 :: uu____790  in
          uu____781 :: uu____784  in
        uu____775 :: uu____778  in
      uu____769 :: uu____772  in
    let uu____1645 = native_tactics_steps ()  in
    FStar_List.append uu____766 uu____1645

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
            let x_tm = FStar_Reflection_Interpreter.embed ea rng x ncb  in
            let app =
              let uu____1663 =
                let uu____1668 =
                  let uu____1669 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____1669]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____1668  in
              uu____1663 FStar_Pervasives_Native.None rng  in
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
               let uu____1719 =
                 let uu____1724 =
                   let uu____1725 =
                     let uu____1734 =
                       FStar_Reflection_Interpreter.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1734  in
                   [uu____1725]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1724  in
               uu____1719 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1775 = FStar_Options.tactics_nbe ()  in
               if uu____1775
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             let result =
               let uu____1797 = primitive_steps ()  in
               norm_f uu____1797 steps
                 proof_state.FStar_Tactics_Types.main_context tm
                in
             let res =
               let uu____1805 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Reflection_Interpreter.unembed uu____1805 result ncb  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1818 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____1818
                   (fun uu____1822  -> FStar_Tactics_Monad.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1827 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____1827
                   (fun uu____1831  -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____1834 =
                   let uu____1840 =
                     let uu____1842 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1842
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1840)  in
                 FStar_Errors.raise_error uu____1834
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
              let uu____1859 =
                let uu____1860 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____1860]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1859  in
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
               let uu____1886 =
                 let uu____1887 =
                   let uu____1892 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1892  in
                 [uu____1887]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1886
                in
             let res =
               let uu____1906 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1906 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1919 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____1919
                   (fun uu____1923  -> FStar_Tactics_Monad.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1928 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____1928
                   (fun uu____1932  -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____1935 =
                   let uu____1941 =
                     let uu____1943 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1943
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1941)  in
                 FStar_Errors.raise_error uu____1935
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
               let x_tm = FStar_Reflection_Interpreter.embed ea rng x ncb  in
               let app =
                 let uu____2016 =
                   let uu____2021 =
                     let uu____2022 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____2022]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____2021  in
                 uu____2016 FStar_Pervasives_Native.None rng  in
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
      let em uu____2112 uu____2113 uu____2114 uu____2115 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n1 =
        let uu____2164 = unembed_tactic_1_alt ea er t0 n1  in
        match uu____2164 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____2204 = f x  in FStar_Tactics_Monad.run uu____2204))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____2220 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____2220
  
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____2260 =
               let uu____2262 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____2264 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2262 uu____2264
                 imp.FStar_TypeChecker_Common.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2260, rng)) is
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
                  (let uu____2347 = FStar_ST.op_Bang tacdbg  in
                   if uu____2347
                   then
                     let uu____2371 =
                       FStar_Syntax_Print.term_to_string tactic  in
                     FStar_Util.print1 "Typechecking tactic: (%s) {\n"
                       uu____2371
                   else ());
                  (let uu____2376 =
                     let uu____2383 = FStar_Syntax_Embeddings.type_of e_arg
                        in
                     let uu____2384 = FStar_Syntax_Embeddings.type_of e_res
                        in
                     FStar_TypeChecker_TcTerm.tc_tactic uu____2383 uu____2384
                       env tactic
                      in
                   match uu____2376 with
                   | (uu____2391,uu____2392,g) ->
                       ((let uu____2395 = FStar_ST.op_Bang tacdbg  in
                         if uu____2395
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
                         (let uu____2455 =
                            FStar_Util.record_time
                              (fun uu____2467  ->
                                 let uu____2468 = tau arg  in
                                 FStar_Tactics_Monad.run_safe uu____2468 ps)
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
                                      env.FStar_TypeChecker_Env.curmodule
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
                                        let uu___225_2611 =
                                          FStar_TypeChecker_Env.trivial_guard
                                           in
                                        {
                                          FStar_TypeChecker_Common.guard_f =
                                            (uu___225_2611.FStar_TypeChecker_Common.guard_f);
                                          FStar_TypeChecker_Common.deferred =
                                            (uu___225_2611.FStar_TypeChecker_Common.deferred);
                                          FStar_TypeChecker_Common.univ_ineqs
                                            =
                                            (uu___225_2611.FStar_TypeChecker_Common.univ_ineqs);
                                          FStar_TypeChecker_Common.implicits
                                            =
                                            (ps1.FStar_Tactics_Types.all_implicits)
                                        }  in
                                      let g2 =
                                        FStar_TypeChecker_Rel.solve_deferred_constraints
                                          env g1
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
                                           env g2
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
                                          FStar_Tactics_Printing.do_dump_proofstate
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
                                      FStar_Tactics_Printing.do_dump_proofstate
                                        uu____2718 "at the time of failure");
                                     (let texn_to_string e1 =
                                        match e1 with
                                        | FStar_Tactics_Types.TacticFailure s
                                            -> s
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
            let uu____2860 =
              FStar_Tactics_Basic.proofstate_of_all_implicits rng_goal env
                imps
               in
            match uu____2860 with
            | (ps,uu____2868) ->
                let uu____2869 =
                  run_tactic_on_ps rng_tac rng_goal
                    FStar_Syntax_Embeddings.e_unit ()
                    FStar_Syntax_Embeddings.e_unit tactic env ps
                   in
                (match uu____2869 with | (goals,()) -> goals)
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2892 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2903 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2914 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2973 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3017 -> false
  
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3075 -> false
  
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____3118 . 'Auu____3118 -> 'Auu____3118 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3148 = FStar_Syntax_Util.head_and_args t  in
        match uu____3148 with
        | (hd1,args) ->
            let uu____3191 =
              let uu____3206 =
                let uu____3207 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3207.FStar_Syntax_Syntax.n  in
              (uu____3206, args)  in
            (match uu____3191 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(tactic,FStar_Pervasives_Native.None )::(assertion,FStar_Pervasives_Native.None
                                                            )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3269 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3269 with
                       | (gs,uu____3277) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3284 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3284 with
                       | (gs,uu____3292) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3335 =
                        let uu____3342 =
                          let uu____3345 =
                            let uu____3346 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3346
                             in
                          [uu____3345]  in
                        (FStar_Syntax_Util.t_true, uu____3342)  in
                      Simplified uu____3335
                  | Both  ->
                      let uu____3357 =
                        let uu____3366 =
                          let uu____3369 =
                            let uu____3370 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3370
                             in
                          [uu____3369]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3366)  in
                      Dual uu____3357
                  | Neg  -> Simplified (assertion, []))
             | uu____3383 -> Unchanged t)
  
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___0_3475  ->
      match uu___0_3475 with
      | Unchanged t -> let uu____3481 = f t  in Unchanged uu____3481
      | Simplified (t,gs) ->
          let uu____3488 = let uu____3495 = f t  in (uu____3495, gs)  in
          Simplified uu____3488
      | Dual (tn,tp,gs) ->
          let uu____3505 =
            let uu____3514 = f tn  in
            let uu____3515 = f tp  in (uu____3514, uu____3515, gs)  in
          Dual uu____3505
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3579 = f t1 t2  in Unchanged uu____3579
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3591 = let uu____3598 = f t1 t2  in (uu____3598, gs)
               in
            Simplified uu____3591
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3612 = let uu____3619 = f t1 t2  in (uu____3619, gs)
               in
            Simplified uu____3612
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3638 =
              let uu____3645 = f t1 t2  in
              (uu____3645, (FStar_List.append gs1 gs2))  in
            Simplified uu____3638
        | uu____3648 ->
            let uu____3657 = explode x  in
            (match uu____3657 with
             | (n1,p1,gs1) ->
                 let uu____3675 = explode y  in
                 (match uu____3675 with
                  | (n2,p2,gs2) ->
                      let uu____3693 =
                        let uu____3702 = f n1 n2  in
                        let uu____3703 = f p1 p2  in
                        (uu____3702, uu____3703, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3693))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3776 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3776
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3825  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3868 =
              let uu____3869 = FStar_Syntax_Subst.compress t  in
              uu____3869.FStar_Syntax_Syntax.n  in
            match uu____3868 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3881 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3881 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3907 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3907 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3927;
                   FStar_Syntax_Syntax.vars = uu____3928;_},(p,uu____3930)::
                 (q,uu____3932)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3990 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3990 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____4004 = FStar_Syntax_Util.mk_imp l r  in
                       uu____4004.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4008;
                   FStar_Syntax_Syntax.vars = uu____4009;_},(p,uu____4011)::
                 (q,uu____4013)::[])
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
                  let uu____4071 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4071 p  in
                let r2 =
                  let uu____4073 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4073 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4080,Unchanged uu____4081) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4099 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4099.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4102 ->
                     let uu____4111 = explode r1  in
                     (match uu____4111 with
                      | (pn,pp,gs1) ->
                          let uu____4129 = explode r2  in
                          (match uu____4129 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4150 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4153 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4150
                                   uu____4153
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4217  ->
                       fun r  ->
                         match uu____4217 with
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
                let uu____4369 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4369 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4409  ->
                            match uu____4409 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4431 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___506_4463 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___506_4463.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___506_4463.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4431 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4491 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4491.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4537 = traverse f pol e t1  in
                let uu____4542 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4542 uu____4537
            | FStar_Syntax_Syntax.Tm_match (sc,brs) ->
                let uu____4617 = traverse f pol e sc  in
                let uu____4622 =
                  let uu____4641 =
                    FStar_List.map
                      (fun br  ->
                         let uu____4658 = FStar_Syntax_Subst.open_branch br
                            in
                         match uu____4658 with
                         | (pat,w,exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs
                                in
                             let r = traverse f pol e1 exp  in
                             let uu____4685 =
                               comb1
                                 (fun exp1  ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1))
                                in
                             uu____4685 r) brs
                     in
                  comb_list uu____4641  in
                comb2
                  (fun sc1  ->
                     fun brs1  -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____4617 uu____4622
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___538_4771 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___538_4771.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___538_4771.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4778 =
                f pol e
                  (let uu___544_4782 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___544_4782.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___544_4782.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4778
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___551_4792 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___551_4792.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___551_4792.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4793 = explode rp  in
              (match uu____4793 with
               | (uu____4802,p',gs') ->
                   Dual
                     ((let uu___558_4812 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___558_4812.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___558_4812.FStar_Syntax_Syntax.vars)
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
      (let uu____4857 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4857);
      (let uu____4882 = FStar_ST.op_Bang tacdbg  in
       if uu____4882
       then
         let uu____4906 =
           let uu____4908 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4908
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4911 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4906
           uu____4911
       else ());
      (let initial = (Prims.int_one, [])  in
       let uu____4946 =
         let uu____4955 = traverse by_tactic_interp Pos env goal  in
         match uu____4955 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4979 -> failwith "no"  in
       match uu____4946 with
       | (t',gs) ->
           ((let uu____5008 = FStar_ST.op_Bang tacdbg  in
             if uu____5008
             then
               let uu____5032 =
                 let uu____5034 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____5034
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____5037 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____5032 uu____5037
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5092  ->
                    fun g  ->
                      match uu____5092 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____5141 =
                              let uu____5144 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____5145 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____5144 uu____5145  in
                            match uu____5141 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5146 =
                                  let uu____5152 =
                                    let uu____5154 =
                                      let uu____5156 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____5156
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5154
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5152)
                                   in
                                FStar_Errors.raise_error uu____5146
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5161 = FStar_ST.op_Bang tacdbg  in
                            if uu____5161
                            then
                              let uu____5185 = FStar_Util.string_of_int n1
                                 in
                              let uu____5187 =
                                let uu____5189 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____5189
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5185 uu____5187
                            else ());
                           (let label1 =
                              let uu____5195 =
                                let uu____5197 =
                                  FStar_Tactics_Types.get_label g  in
                                uu____5197 = ""  in
                              if uu____5195
                              then
                                let uu____5203 = FStar_Util.string_of_int n1
                                   in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____5203
                              else
                                (let uu____5208 =
                                   let uu____5210 =
                                     FStar_Util.string_of_int n1  in
                                   let uu____5212 =
                                     let uu____5214 =
                                       let uu____5216 =
                                         FStar_Tactics_Types.get_label g  in
                                       Prims.op_Hat uu____5216 ")"  in
                                     Prims.op_Hat " (" uu____5214  in
                                   Prims.op_Hat uu____5210 uu____5212  in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____5208)
                               in
                            let gt' =
                              FStar_TypeChecker_Util.label label1
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____5222 =
                              let uu____5231 =
                                let uu____5238 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____5238, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____5231 :: gs1  in
                            ((n1 + Prims.int_one), uu____5222)))) s gs
                in
             let uu____5255 = s1  in
             match uu____5255 with
             | (uu____5277,gs1) ->
                 let gs2 = FStar_List.rev gs1  in
                 let uu____5312 =
                   let uu____5319 = FStar_Options.peek ()  in
                   (env, t', uu____5319)  in
                 uu____5312 :: gs2)))
  
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
          let uu____5343 =
            let uu____5348 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____5349 =
              let uu____5350 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5350]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____5348 uu____5349  in
          uu____5343 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____5378 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5378);
           (let uu____5402 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____5402 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____5423 =
                        let uu____5426 = FStar_Tactics_Types.goal_env g  in
                        let uu____5427 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____5426 uu____5427  in
                      match uu____5423 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____5430 = FStar_ST.op_Bang tacdbg  in
                            if uu____5430
                            then
                              let uu____5454 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____5454
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
                            let uu____5469 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____5469 guard))
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
          ((let uu____5492 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5492);
           (let gs =
              let uu____5519 = FStar_TypeChecker_Env.get_range env  in
              run_tactic_on_all_implicits tau.FStar_Syntax_Syntax.pos
                uu____5519 tau env imps
               in
            FStar_All.pipe_right gs
              (FStar_List.iter
                 (fun g  ->
                    let uu____5530 =
                      let uu____5533 = FStar_Tactics_Types.goal_env g  in
                      let uu____5534 = FStar_Tactics_Types.goal_type g  in
                      getprop uu____5533 uu____5534  in
                    match uu____5530 with
                    | FStar_Pervasives_Native.Some vc ->
                        ((let uu____5537 = FStar_ST.op_Bang tacdbg  in
                          if uu____5537
                          then
                            let uu____5561 =
                              FStar_Syntax_Print.term_to_string vc  in
                            FStar_Util.print1 "Synthesis left a goal: %s\n"
                              uu____5561
                          else ());
                         (let guard =
                            {
                              FStar_TypeChecker_Common.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Common.deferred = [];
                              FStar_TypeChecker_Common.univ_ineqs = ([], []);
                              FStar_TypeChecker_Common.implicits = []
                            }  in
                          let uu____5576 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____5576 guard))
                    | FStar_Pervasives_Native.None  ->
                        let uu____5577 = FStar_TypeChecker_Env.get_range env
                           in
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                            "synthesis left open goals") uu____5577))))
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      if env.FStar_TypeChecker_Env.nosynth
      then []
      else
        ((let uu____5599 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____5599);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let ps =
            FStar_Tactics_Basic.proofstate_of_goals
              tau.FStar_Syntax_Syntax.pos env [] []
             in
          let uu____5625 =
            let uu____5634 =
              FStar_Syntax_Embeddings.e_list
                FStar_Reflection_Embeddings.e_sigelt
               in
            run_tactic_on_ps tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos FStar_Syntax_Embeddings.e_unit ()
              uu____5634 tau env ps
             in
          match uu____5625 with
          | (gs,sigelts) ->
              ((let uu____5654 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____5659 =
                         let uu____5661 =
                           let uu____5664 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____5665 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____5664 uu____5665  in
                         FStar_Option.isSome uu____5661  in
                       Prims.op_Negation uu____5659) gs
                   in
                if uu____5654
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                      "splice left open goals") typ.FStar_Syntax_Syntax.pos
                else ());
               (let uu____5672 = FStar_ST.op_Bang tacdbg  in
                if uu____5672
                then
                  let uu____5696 =
                    FStar_Common.string_of_list
                      FStar_Syntax_Print.sigelt_to_string sigelts
                     in
                  FStar_Util.print1 "splice: got decls = %s\n" uu____5696
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
          ((let uu____5721 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5721);
           (let ps =
              FStar_Tactics_Basic.proofstate_of_goals
                tm.FStar_Syntax_Syntax.pos env [] []
               in
            let uu____5746 =
              run_tactic_on_ps tau.FStar_Syntax_Syntax.pos
                tm.FStar_Syntax_Syntax.pos FStar_Reflection_Embeddings.e_term
                tm FStar_Reflection_Embeddings.e_term tau env ps
               in
            match uu____5746 with | (gs,tm1) -> tm1))
  
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
            ((let uu____5784 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")
                 in
              FStar_ST.op_Colon_Equals tacdbg uu____5784);
             (let uu____5808 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None
                 in
              match uu____5808 with
              | (uvtm,uu____5827,g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ  in
                  let goal =
                    let uu____5845 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm
                       in
                    FStar_Syntax_Util.mk_squash u uu____5845  in
                  let uu____5846 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal
                     in
                  (match uu____5846 with
                   | (gs,w) ->
                       (FStar_List.iter
                          (fun g  ->
                             let uu____5867 =
                               let uu____5870 =
                                 FStar_Tactics_Types.goal_env g  in
                               let uu____5871 =
                                 FStar_Tactics_Types.goal_type g  in
                               getprop uu____5870 uu____5871  in
                             match uu____5867 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____5874 = FStar_ST.op_Bang tacdbg
                                      in
                                   if uu____5874
                                   then
                                     let uu____5898 =
                                       FStar_Syntax_Print.term_to_string vc
                                        in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____5898
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
                                   let uu____5913 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____5913 guard))
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
  