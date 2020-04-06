open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let unembed :
  'uuuuuu14 .
    'uuuuuu14 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'uuuuuu14 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____38 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____38 true norm_cb
  
let embed :
  'uuuuuu57 .
    'uuuuuu57 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'uuuuuu57 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea  ->
    fun r  ->
      fun x  ->
        fun norm_cb  ->
          let uu____84 = FStar_Syntax_Embeddings.embed ea x  in
          uu____84 r FStar_Pervasives_Native.None norm_cb
  
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____100  ->
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
    let uu____113 = FStar_Tactics_Native.list_all ()  in
    FStar_List.map step_from_native_step uu____113
  
let mktot1' :
  'uuuuuu141 'uuuuuu142 'uuuuuu143 'uuuuuu144 .
    Prims.int ->
      Prims.string ->
        ('uuuuuu141 -> 'uuuuuu142) ->
          'uuuuuu141 FStar_Syntax_Embeddings.embedding ->
            'uuuuuu142 FStar_Syntax_Embeddings.embedding ->
              ('uuuuuu143 -> 'uuuuuu144) ->
                'uuuuuu143 FStar_TypeChecker_NBETerm.embedding ->
                  'uuuuuu144 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___20_215 =
                    FStar_Tactics_InterpFuns.mktot1 uarity nm f ea er nf ena
                      enr
                     in
                  let uu____216 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____216;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___20_215.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___20_215.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___20_215.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___20_215.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___20_215.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___20_215.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___20_215.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot1'_psc :
  'uuuuuu243 'uuuuuu244 'uuuuuu245 'uuuuuu246 .
    Prims.int ->
      Prims.string ->
        (FStar_TypeChecker_Cfg.psc -> 'uuuuuu243 -> 'uuuuuu244) ->
          'uuuuuu243 FStar_Syntax_Embeddings.embedding ->
            'uuuuuu244 FStar_Syntax_Embeddings.embedding ->
              (FStar_TypeChecker_Cfg.psc -> 'uuuuuu245 -> 'uuuuuu246) ->
                'uuuuuu245 FStar_TypeChecker_NBETerm.embedding ->
                  'uuuuuu246 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___30_327 =
                    FStar_Tactics_InterpFuns.mktot1_psc uarity nm f ea er nf
                      ena enr
                     in
                  let uu____328 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____328;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___30_327.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___30_327.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___30_327.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___30_327.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___30_327.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___30_327.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___30_327.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot2' :
  'uuuuuu363 'uuuuuu364 'uuuuuu365 'uuuuuu366 'uuuuuu367 'uuuuuu368 .
    Prims.int ->
      Prims.string ->
        ('uuuuuu363 -> 'uuuuuu364 -> 'uuuuuu365) ->
          'uuuuuu363 FStar_Syntax_Embeddings.embedding ->
            'uuuuuu364 FStar_Syntax_Embeddings.embedding ->
              'uuuuuu365 FStar_Syntax_Embeddings.embedding ->
                ('uuuuuu366 -> 'uuuuuu367 -> 'uuuuuu368) ->
                  'uuuuuu366 FStar_TypeChecker_NBETerm.embedding ->
                    'uuuuuu367 FStar_TypeChecker_NBETerm.embedding ->
                      'uuuuuu368 FStar_TypeChecker_NBETerm.embedding ->
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
                      let uu___42_467 =
                        FStar_Tactics_InterpFuns.mktot2 uarity nm f ea eb er
                          nf ena enb enr
                         in
                      let uu____468 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm)
                         in
                      {
                        FStar_TypeChecker_Cfg.name = uu____468;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___42_467.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___42_467.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___42_467.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___42_467.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___42_467.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___42_467.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___42_467.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
  
let rec e_tactic_thunk :
  'r .
    'r FStar_Syntax_Embeddings.embedding ->
      'r FStar_Tactics_Monad.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____700 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____707  ->
         fun uu____708  ->
           fun uu____709  ->
             fun uu____710  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____724 =
               let uu____727 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____727 ()  in
             FStar_Pervasives_Native.Some uu____724) uu____700

and e_tactic_nbe_thunk :
  'r .
    'r FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_Tactics_Monad.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____739 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____745  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____754 =
             let uu____757 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____757 ()  in
           FStar_Pervasives_Native.Some uu____754)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____739

and e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac) FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____772 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____782  ->
           fun uu____783  ->
             fun uu____784  ->
               fun uu____785  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____801 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____801) uu____772

and e_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____819 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____828  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____839 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____839)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____819

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____851  ->
    let uu____854 =
      let uu____857 =
        mktot1'_psc Prims.int_zero "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____860 =
        let uu____863 =
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
        let uu____866 =
          let uu____869 =
            mktot1' Prims.int_zero "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe
             in
          let uu____872 =
            let uu____875 =
              mktot1' Prims.int_zero "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____878 =
              let uu____881 =
                let uu____882 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal
                   in
                let uu____887 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe
                   in
                mktot1' Prims.int_zero "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____882
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____887
                 in
              let uu____898 =
                let uu____901 =
                  let uu____902 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____907 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mktot1' Prims.int_zero "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____902
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____907
                   in
                let uu____918 =
                  let uu____921 =
                    mktot1' Prims.int_zero "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env
                     in
                  let uu____924 =
                    let uu____927 =
                      mktot1' Prims.int_zero "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term
                       in
                    let uu____930 =
                      let uu____933 =
                        mktot1' Prims.int_zero "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____936 =
                        let uu____939 =
                          mktot1' Prims.int_zero "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool
                           in
                        let uu____944 =
                          let uu____947 =
                            mktot1' Prims.int_zero "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string
                             in
                          let uu____952 =
                            let uu____955 =
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
                            let uu____960 =
                              let uu____963 =
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
                              let uu____1022 =
                                let uu____1025 =
                                  let uu____1026 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal
                                     in
                                  let uu____1031 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe
                                     in
                                  FStar_Tactics_InterpFuns.mktac1
                                    Prims.int_zero "set_goals"
                                    FStar_Tactics_Monad.set_goals uu____1026
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Monad.set_goals uu____1031
                                    FStar_TypeChecker_NBETerm.e_unit
                                   in
                                let uu____1042 =
                                  let uu____1045 =
                                    let uu____1046 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Tactics_Embedding.e_goal
                                       in
                                    let uu____1051 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Tactics_Embedding.e_goal_nbe
                                       in
                                    FStar_Tactics_InterpFuns.mktac1
                                      Prims.int_zero "set_smt_goals"
                                      FStar_Tactics_Monad.set_smt_goals
                                      uu____1046
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Monad.set_smt_goals
                                      uu____1051
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____1062 =
                                    let uu____1065 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        Prims.int_zero "trivial"
                                        FStar_Tactics_Basic.trivial
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.trivial
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____1068 =
                                      let uu____1071 =
                                        let uu____1072 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____1077 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____1084 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        let uu____1089 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        FStar_Tactics_InterpFuns.mktac2
                                          Prims.int_one "catch"
                                          (fun uu____1111  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____1072 uu____1077
                                          (fun uu____1113  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____1084 uu____1089
                                         in
                                      let uu____1114 =
                                        let uu____1117 =
                                          let uu____1118 =
                                            e_tactic_thunk
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____1123 =
                                            FStar_Syntax_Embeddings.e_either
                                              FStar_Tactics_Embedding.e_exn
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____1130 =
                                            e_tactic_nbe_thunk
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          let uu____1135 =
                                            FStar_TypeChecker_NBETerm.e_either
                                              FStar_Tactics_Embedding.e_exn_nbe
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          FStar_Tactics_InterpFuns.mktac2
                                            Prims.int_one "recover"
                                            (fun uu____1157  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_Syntax_Embeddings.e_any
                                            uu____1118 uu____1123
                                            (fun uu____1159  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_TypeChecker_NBETerm.e_any
                                            uu____1130 uu____1135
                                           in
                                        let uu____1160 =
                                          let uu____1163 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              Prims.int_zero "intro"
                                              FStar_Tactics_Basic.intro
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Tactics_Basic.intro
                                              FStar_TypeChecker_NBETerm.e_unit
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                             in
                                          let uu____1166 =
                                            let uu____1169 =
                                              let uu____1170 =
                                                FStar_Syntax_Embeddings.e_tuple2
                                                  FStar_Reflection_Embeddings.e_binder
                                                  FStar_Reflection_Embeddings.e_binder
                                                 in
                                              let uu____1177 =
                                                FStar_TypeChecker_NBETerm.e_tuple2
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                 in
                                              FStar_Tactics_InterpFuns.mktac1
                                                Prims.int_zero "intro_rec"
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_Syntax_Embeddings.e_unit
                                                uu____1170
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_TypeChecker_NBETerm.e_unit
                                                uu____1177
                                               in
                                            let uu____1194 =
                                              let uu____1197 =
                                                let uu____1198 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step
                                                   in
                                                let uu____1203 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step
                                                   in
                                                FStar_Tactics_InterpFuns.mktac1
                                                  Prims.int_zero "norm"
                                                  FStar_Tactics_Basic.norm
                                                  uu____1198
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.norm
                                                  uu____1203
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                 in
                                              let uu____1214 =
                                                let uu____1217 =
                                                  let uu____1218 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step
                                                     in
                                                  let uu____1223 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step
                                                     in
                                                  FStar_Tactics_InterpFuns.mktac3
                                                    Prims.int_zero
                                                    "norm_term_env"
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_Embeddings.e_env
                                                    uu____1218
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    uu____1223
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                   in
                                                let uu____1234 =
                                                  let uu____1237 =
                                                    let uu____1238 =
                                                      FStar_Syntax_Embeddings.e_list
                                                        FStar_Syntax_Embeddings.e_norm_step
                                                       in
                                                    let uu____1243 =
                                                      FStar_TypeChecker_NBETerm.e_list
                                                        FStar_TypeChecker_NBETerm.e_norm_step
                                                       in
                                                    FStar_Tactics_InterpFuns.mktac2
                                                      Prims.int_zero
                                                      "norm_binder_type"
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____1238
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Syntax_Embeddings.e_unit
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____1243
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                      FStar_TypeChecker_NBETerm.e_unit
                                                     in
                                                  let uu____1254 =
                                                    let uu____1257 =
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
                                                    let uu____1262 =
                                                      let uu____1265 =
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
                                                      let uu____1268 =
                                                        let uu____1271 =
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
                                                        let uu____1274 =
                                                          let uu____1277 =
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
                                                          let uu____1280 =
                                                            let uu____1283 =
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
                                                            let uu____1286 =
                                                              let uu____1289
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
                                                              let uu____1292
                                                                =
                                                                let uu____1295
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
                                                                let uu____1298
                                                                  =
                                                                  let uu____1301
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
                                                                  let uu____1308
                                                                    =
                                                                    let uu____1311
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
                                                                    let uu____1318
                                                                    =
                                                                    let uu____1321
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
                                                                    let uu____1324
                                                                    =
                                                                    let uu____1327
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
                                                                    let uu____1332
                                                                    =
                                                                    let uu____1335
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
                                                                    let uu____1338
                                                                    =
                                                                    let uu____1341
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
                                                                    let uu____1344
                                                                    =
                                                                    let uu____1347
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
                                                                    let uu____1350
                                                                    =
                                                                    let uu____1353
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1358
                                                                     ->
                                                                    fun
                                                                    uu____1359
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1363
                                                                    =
                                                                    let uu____1366
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
                                                                    let uu____1371
                                                                    =
                                                                    let uu____1374
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
                                                                    let uu____1379
                                                                    =
                                                                    let uu____1382
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
                                                                    let uu____1387
                                                                    =
                                                                    let uu____1390
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
                                                                    let uu____1395
                                                                    =
                                                                    let uu____1398
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
                                                                    let uu____1403
                                                                    =
                                                                    let uu____1406
                                                                    =
                                                                    let uu____1407
                                                                    =
                                                                    let uu____1420
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1420
                                                                     in
                                                                    let uu____1434
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1439
                                                                    =
                                                                    let uu____1452
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1452
                                                                     in
                                                                    let uu____1466
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1407
                                                                    uu____1434
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1439
                                                                    uu____1466
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1497
                                                                    =
                                                                    let uu____1500
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
                                                                    let uu____1503
                                                                    =
                                                                    let uu____1506
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
                                                                    let uu____1509
                                                                    =
                                                                    let uu____1512
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
                                                                    let uu____1515
                                                                    =
                                                                    let uu____1518
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
                                                                    let uu____1521
                                                                    =
                                                                    let uu____1524
                                                                    =
                                                                    let uu____1525
                                                                    =
                                                                    let uu____1534
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1534
                                                                     in
                                                                    let uu____1545
                                                                    =
                                                                    let uu____1554
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1554
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1525
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1545
                                                                     in
                                                                    let uu____1579
                                                                    =
                                                                    let uu____1582
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
                                                                    let uu____1585
                                                                    =
                                                                    let uu____1588
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
                                                                    let uu____1591
                                                                    =
                                                                    let uu____1594
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
                                                                    let uu____1597
                                                                    =
                                                                    let uu____1600
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
                                                                    let uu____1603
                                                                    =
                                                                    let uu____1606
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
                                                                    let uu____1609
                                                                    =
                                                                    let uu____1612
                                                                    =
                                                                    let uu____1613
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1618
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1613
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1618
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1629
                                                                    =
                                                                    let uu____1632
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
                                                                    let uu____1637
                                                                    =
                                                                    let uu____1640
                                                                    =
                                                                    let uu____1641
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1648
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1641
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1648
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1669
                                                                    =
                                                                    let uu____1672
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
                                                                    let uu____1677
                                                                    =
                                                                    let uu____1680
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
                                                                    let uu____1683
                                                                    =
                                                                    let uu____1686
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
                                                                    let uu____1689
                                                                    =
                                                                    let uu____1692
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
                                                                    let uu____1695
                                                                    =
                                                                    let uu____1698
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
                                                                    let uu____1703
                                                                    =
                                                                    let uu____1706
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1713
                                                                     ->
                                                                    fun
                                                                    uu____1714
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1717
                                                                    =
                                                                    let uu____1720
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
                                                                    uu____1728
                                                                     ->
                                                                    fun
                                                                    uu____1729
                                                                     ->
                                                                    fun
                                                                    uu____1730
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____1720]
                                                                     in
                                                                    uu____1706
                                                                    ::
                                                                    uu____1717
                                                                     in
                                                                    uu____1698
                                                                    ::
                                                                    uu____1703
                                                                     in
                                                                    uu____1692
                                                                    ::
                                                                    uu____1695
                                                                     in
                                                                    uu____1686
                                                                    ::
                                                                    uu____1689
                                                                     in
                                                                    uu____1680
                                                                    ::
                                                                    uu____1683
                                                                     in
                                                                    uu____1672
                                                                    ::
                                                                    uu____1677
                                                                     in
                                                                    uu____1640
                                                                    ::
                                                                    uu____1669
                                                                     in
                                                                    uu____1632
                                                                    ::
                                                                    uu____1637
                                                                     in
                                                                    uu____1612
                                                                    ::
                                                                    uu____1629
                                                                     in
                                                                    uu____1606
                                                                    ::
                                                                    uu____1609
                                                                     in
                                                                    uu____1600
                                                                    ::
                                                                    uu____1603
                                                                     in
                                                                    uu____1594
                                                                    ::
                                                                    uu____1597
                                                                     in
                                                                    uu____1588
                                                                    ::
                                                                    uu____1591
                                                                     in
                                                                    uu____1582
                                                                    ::
                                                                    uu____1585
                                                                     in
                                                                    uu____1524
                                                                    ::
                                                                    uu____1579
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
                                                                    uu____1406
                                                                    ::
                                                                    uu____1497
                                                                     in
                                                                    uu____1398
                                                                    ::
                                                                    uu____1403
                                                                     in
                                                                    uu____1390
                                                                    ::
                                                                    uu____1395
                                                                     in
                                                                    uu____1382
                                                                    ::
                                                                    uu____1387
                                                                     in
                                                                    uu____1374
                                                                    ::
                                                                    uu____1379
                                                                     in
                                                                    uu____1366
                                                                    ::
                                                                    uu____1371
                                                                     in
                                                                    uu____1353
                                                                    ::
                                                                    uu____1363
                                                                     in
                                                                    uu____1347
                                                                    ::
                                                                    uu____1350
                                                                     in
                                                                    uu____1341
                                                                    ::
                                                                    uu____1344
                                                                     in
                                                                    uu____1335
                                                                    ::
                                                                    uu____1338
                                                                     in
                                                                    uu____1327
                                                                    ::
                                                                    uu____1332
                                                                     in
                                                                    uu____1321
                                                                    ::
                                                                    uu____1324
                                                                     in
                                                                    uu____1311
                                                                    ::
                                                                    uu____1318
                                                                     in
                                                                  uu____1301
                                                                    ::
                                                                    uu____1308
                                                                   in
                                                                uu____1295 ::
                                                                  uu____1298
                                                                 in
                                                              uu____1289 ::
                                                                uu____1292
                                                               in
                                                            uu____1283 ::
                                                              uu____1286
                                                             in
                                                          uu____1277 ::
                                                            uu____1280
                                                           in
                                                        uu____1271 ::
                                                          uu____1274
                                                         in
                                                      uu____1265 ::
                                                        uu____1268
                                                       in
                                                    uu____1257 :: uu____1262
                                                     in
                                                  uu____1237 :: uu____1254
                                                   in
                                                uu____1217 :: uu____1234  in
                                              uu____1197 :: uu____1214  in
                                            uu____1169 :: uu____1194  in
                                          uu____1163 :: uu____1166  in
                                        uu____1117 :: uu____1160  in
                                      uu____1071 :: uu____1114  in
                                    uu____1065 :: uu____1068  in
                                  uu____1045 :: uu____1062  in
                                uu____1025 :: uu____1042  in
                              uu____963 :: uu____1022  in
                            uu____955 :: uu____960  in
                          uu____947 :: uu____952  in
                        uu____939 :: uu____944  in
                      uu____933 :: uu____936  in
                    uu____927 :: uu____930  in
                  uu____921 :: uu____924  in
                uu____901 :: uu____918  in
              uu____881 :: uu____898  in
            uu____875 :: uu____878  in
          uu____869 :: uu____872  in
        uu____863 :: uu____866  in
      uu____857 :: uu____860  in
    let uu____1733 = native_tactics_steps ()  in
    FStar_List.append uu____854 uu____1733

and unembed_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb -> 'a -> 'r FStar_Tactics_Monad.tac
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          fun x  ->
            let rng = FStar_Range.dummyRange  in
            let x_tm = embed ea rng x ncb  in
            let app =
              let uu____1751 =
                let uu____1756 =
                  let uu____1757 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____1757]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____1756  in
              uu____1751 FStar_Pervasives_Native.None rng  in
            unembed_tactic_0 er app ncb

and unembed_tactic_0 :
  'b .
    'b FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb -> 'b FStar_Tactics_Monad.tac
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
               let uu____1807 =
                 let uu____1812 =
                   let uu____1813 =
                     let uu____1822 =
                       embed FStar_Tactics_Embedding.e_proofstate rng
                         proof_state ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1822  in
                   [uu____1813]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1812  in
               uu____1807 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1863 = FStar_Options.tactics_nbe ()  in
               if uu____1863
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             let result =
               let uu____1885 = primitive_steps ()  in
               norm_f uu____1885 steps
                 proof_state.FStar_Tactics_Types.main_context tm
                in
             let res =
               let uu____1893 = FStar_Tactics_Embedding.e_result eb  in
               unembed uu____1893 result ncb  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1906 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____1906
                   (fun uu____1910  -> FStar_Tactics_Monad.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1915 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____1915
                   (fun uu____1919  -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____1922 =
                   let uu____1928 =
                     let uu____1930 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1930
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1928)  in
                 FStar_Errors.raise_error uu____1922
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

and unembed_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.nbe_cbs ->
          FStar_TypeChecker_NBETerm.t -> 'a -> 'r FStar_Tactics_Monad.tac
  =
  fun ea  ->
    fun er  ->
      fun cb  ->
        fun f  ->
          fun x  ->
            let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x  in
            let app =
              let uu____1947 =
                let uu____1948 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____1948]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1947  in
            unembed_tactic_nbe_0 er cb app

and unembed_tactic_nbe_0 :
  'b .
    'b FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.nbe_cbs ->
        FStar_TypeChecker_NBETerm.t -> 'b FStar_Tactics_Monad.tac
  =
  fun eb  ->
    fun cb  ->
      fun embedded_tac_b  ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun proof_state  ->
             let result =
               let uu____1974 =
                 let uu____1975 =
                   let uu____1980 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1980  in
                 [uu____1975]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1974
                in
             let res =
               let uu____1994 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1994 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____2007 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____2007
                   (fun uu____2011  -> FStar_Tactics_Monad.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____2016 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____2016
                   (fun uu____2020  -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____2023 =
                   let uu____2029 =
                     let uu____2031 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2031
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2029)  in
                 FStar_Errors.raise_error uu____2023
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

let unembed_tactic_1_alt :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            ('a -> 'r FStar_Tactics_Monad.tac) FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          FStar_Pervasives_Native.Some
            (fun x  ->
               let rng = FStar_Range.dummyRange  in
               let x_tm = embed ea rng x ncb  in
               let app =
                 let uu____2104 =
                   let uu____2109 =
                     let uu____2110 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____2110]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____2109  in
                 uu____2104 FStar_Pervasives_Native.None rng  in
               unembed_tactic_0 er app ncb)
  
let e_tactic_1_alt :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a ->
           FStar_Tactics_Types.proofstate -> 'r FStar_Tactics_Result.__result)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let em uu____2200 uu____2201 uu____2202 uu____2203 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n =
        let uu____2252 = unembed_tactic_1_alt ea er t0 n  in
        match uu____2252 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____2292 = f x  in FStar_Tactics_Monad.run uu____2292))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____2308 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____2308
  
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____2348 =
               let uu____2350 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____2352 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2350 uu____2352
                 imp.FStar_TypeChecker_Common.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2348, rng)) is
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
                  (let uu____2435 = FStar_ST.op_Bang tacdbg  in
                   if uu____2435
                   then
                     let uu____2459 =
                       FStar_Syntax_Print.term_to_string tactic  in
                     FStar_Util.print1 "Typechecking tactic: (%s) {\n"
                       uu____2459
                   else ());
                  (let uu____2464 =
                     let uu____2471 = FStar_Syntax_Embeddings.type_of e_arg
                        in
                     let uu____2472 = FStar_Syntax_Embeddings.type_of e_res
                        in
                     FStar_TypeChecker_TcTerm.tc_tactic uu____2471 uu____2472
                       env tactic
                      in
                   match uu____2464 with
                   | (uu____2479,uu____2480,g) ->
                       ((let uu____2483 = FStar_ST.op_Bang tacdbg  in
                         if uu____2483
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
                         (let uu____2543 =
                            FStar_Util.record_time
                              (fun uu____2555  ->
                                 let uu____2556 = tau arg  in
                                 FStar_Tactics_Monad.run_safe uu____2556 ps)
                             in
                          match uu____2543 with
                          | (res,ms) ->
                              ((let uu____2574 = FStar_ST.op_Bang tacdbg  in
                                if uu____2574
                                then FStar_Util.print_string "}\n"
                                else ());
                               (let uu____2602 =
                                  (FStar_ST.op_Bang tacdbg) ||
                                    (FStar_Options.tactics_info ())
                                   in
                                if uu____2602
                                then
                                  let uu____2626 =
                                    FStar_Syntax_Print.term_to_string tactic
                                     in
                                  let uu____2628 =
                                    FStar_Util.string_of_int ms  in
                                  let uu____2630 =
                                    FStar_Syntax_Print.lid_to_string
                                      env.FStar_TypeChecker_Env.curmodule
                                     in
                                  FStar_Util.print3
                                    "Tactic %s ran in %s ms (%s)\n"
                                    uu____2626 uu____2628 uu____2630
                                else ());
                               (match res with
                                | FStar_Tactics_Result.Success (ret,ps1) ->
                                    (FStar_List.iter
                                       (fun g1  ->
                                          let uu____2648 =
                                            FStar_Tactics_Types.is_irrelevant
                                              g1
                                             in
                                          if uu____2648
                                          then
                                            let uu____2651 =
                                              let uu____2653 =
                                                FStar_Tactics_Types.goal_env
                                                  g1
                                                 in
                                              let uu____2654 =
                                                FStar_Tactics_Types.goal_witness
                                                  g1
                                                 in
                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                uu____2653 uu____2654
                                                FStar_Syntax_Util.exp_unit
                                               in
                                            (if uu____2651
                                             then ()
                                             else
                                               (let uu____2658 =
                                                  let uu____2660 =
                                                    let uu____2662 =
                                                      FStar_Tactics_Types.goal_witness
                                                        g1
                                                       in
                                                    FStar_Syntax_Print.term_to_string
                                                      uu____2662
                                                     in
                                                  FStar_Util.format1
                                                    "Irrelevant tactic witness does not unify with (): %s"
                                                    uu____2660
                                                   in
                                                failwith uu____2658))
                                          else ())
                                       (FStar_List.append
                                          ps1.FStar_Tactics_Types.goals
                                          ps1.FStar_Tactics_Types.smt_goals);
                                     (let uu____2667 =
                                        FStar_ST.op_Bang tacdbg  in
                                      if uu____2667
                                      then
                                        let uu____2691 =
                                          FStar_Common.string_of_list
                                            (fun imp  ->
                                               FStar_Syntax_Print.ctx_uvar_to_string
                                                 imp.FStar_TypeChecker_Common.imp_uvar)
                                            ps1.FStar_Tactics_Types.all_implicits
                                           in
                                        FStar_Util.print1
                                          "About to check tactic implicits: %s\n"
                                          uu____2691
                                      else ());
                                     (let g1 =
                                        let uu___232_2699 =
                                          FStar_TypeChecker_Env.trivial_guard
                                           in
                                        {
                                          FStar_TypeChecker_Common.guard_f =
                                            (uu___232_2699.FStar_TypeChecker_Common.guard_f);
                                          FStar_TypeChecker_Common.deferred =
                                            (uu___232_2699.FStar_TypeChecker_Common.deferred);
                                          FStar_TypeChecker_Common.univ_ineqs
                                            =
                                            (uu___232_2699.FStar_TypeChecker_Common.univ_ineqs);
                                          FStar_TypeChecker_Common.implicits
                                            =
                                            (ps1.FStar_Tactics_Types.all_implicits)
                                        }  in
                                      let g2 =
                                        FStar_TypeChecker_Rel.solve_deferred_constraints
                                          env g1
                                         in
                                      (let uu____2702 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____2702
                                       then
                                         let uu____2726 =
                                           FStar_Util.string_of_int
                                             (FStar_List.length
                                                ps1.FStar_Tactics_Types.all_implicits)
                                            in
                                         let uu____2728 =
                                           FStar_Common.string_of_list
                                             (fun imp  ->
                                                FStar_Syntax_Print.ctx_uvar_to_string
                                                  imp.FStar_TypeChecker_Common.imp_uvar)
                                             ps1.FStar_Tactics_Types.all_implicits
                                            in
                                         FStar_Util.print2
                                           "Checked %s implicits (1): %s\n"
                                           uu____2726 uu____2728
                                       else ());
                                      (let g3 =
                                         FStar_TypeChecker_Rel.resolve_implicits_tac
                                           env g2
                                          in
                                       (let uu____2737 =
                                          FStar_ST.op_Bang tacdbg  in
                                        if uu____2737
                                        then
                                          let uu____2761 =
                                            FStar_Util.string_of_int
                                              (FStar_List.length
                                                 ps1.FStar_Tactics_Types.all_implicits)
                                             in
                                          let uu____2763 =
                                            FStar_Common.string_of_list
                                              (fun imp  ->
                                                 FStar_Syntax_Print.ctx_uvar_to_string
                                                   imp.FStar_TypeChecker_Common.imp_uvar)
                                              ps1.FStar_Tactics_Types.all_implicits
                                             in
                                          FStar_Util.print2
                                            "Checked %s implicits (2): %s\n"
                                            uu____2761 uu____2763
                                        else ());
                                       report_implicits rng_goal
                                         g3.FStar_TypeChecker_Common.implicits;
                                       (let uu____2772 =
                                          FStar_ST.op_Bang tacdbg  in
                                        if uu____2772
                                        then
                                          let uu____2796 =
                                            let uu____2797 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____2797 ps1
                                             in
                                          FStar_Tactics_Printing.do_dump_proofstate
                                            uu____2796 "at the finish line"
                                        else ());
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         ret))))
                                | FStar_Tactics_Result.Failed (e,ps1) ->
                                    ((let uu____2806 =
                                        let uu____2807 =
                                          FStar_TypeChecker_Cfg.psc_subst
                                            ps1.FStar_Tactics_Types.psc
                                           in
                                        FStar_Tactics_Types.subst_proof_state
                                          uu____2807 ps1
                                         in
                                      FStar_Tactics_Printing.do_dump_proofstate
                                        uu____2806 "at the time of failure");
                                     (let texn_to_string e1 =
                                        match e1 with
                                        | FStar_Tactics_Types.TacticFailure s
                                            -> s
                                        | FStar_Tactics_Types.EExn t ->
                                            let uu____2820 =
                                              FStar_Syntax_Print.term_to_string
                                                t
                                               in
                                            Prims.op_Hat
                                              "uncaught exception: "
                                              uu____2820
                                        | e2 -> FStar_Exn.raise e2  in
                                      let uu____2825 =
                                        let uu____2831 =
                                          let uu____2833 = texn_to_string e
                                             in
                                          FStar_Util.format1
                                            "user tactic failed: %s"
                                            uu____2833
                                           in
                                        (FStar_Errors.Fatal_UserTacticFailure,
                                          uu____2831)
                                         in
                                      FStar_Errors.raise_error uu____2825
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
              let uu____2882 = FStar_Range.use_range rng_goal  in
              let uu____2883 = FStar_Range.use_range rng_tac  in
              FStar_Range.range_of_rng uu____2882 uu____2883  in
            let uu____2884 =
              FStar_Tactics_Basic.proofstate_of_goal_ty rng env typ  in
            match uu____2884 with
            | (ps,w) ->
                let uu____2897 =
                  run_tactic_on_ps rng_tac rng_goal
                    FStar_Syntax_Embeddings.e_unit ()
                    FStar_Syntax_Embeddings.e_unit tactic env ps
                   in
                (match uu____2897 with | (gs,_res) -> (gs, w))
  
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
            let uu____2948 =
              FStar_Tactics_Basic.proofstate_of_all_implicits rng_goal env
                imps
               in
            match uu____2948 with
            | (ps,uu____2956) ->
                let uu____2957 =
                  run_tactic_on_ps rng_tac rng_goal
                    FStar_Syntax_Embeddings.e_unit ()
                    FStar_Syntax_Embeddings.e_unit tactic env ps
                   in
                (match uu____2957 with | (goals,()) -> goals)
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2980 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2991 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____3002 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3061 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3105 -> false
  
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3163 -> false
  
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'uuuuuu3206 . 'uuuuuu3206 -> 'uuuuuu3206 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol1  ->
    fun e  ->
      fun t  ->
        let uu____3236 = FStar_Syntax_Util.head_and_args t  in
        match uu____3236 with
        | (hd,args) ->
            let uu____3279 =
              let uu____3294 =
                let uu____3295 = FStar_Syntax_Util.un_uinst hd  in
                uu____3295.FStar_Syntax_Syntax.n  in
              (uu____3294, args)  in
            (match uu____3279 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(tactic,FStar_Pervasives_Native.None )::(assertion,FStar_Pervasives_Native.None
                                                            )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol1 with
                  | Pos  ->
                      let uu____3357 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3357 with
                       | (gs,uu____3365) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3372 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3372 with
                       | (gs,uu____3380) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol1 with
                  | Pos  ->
                      let uu____3423 =
                        let uu____3430 =
                          let uu____3433 =
                            let uu____3434 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3434
                             in
                          [uu____3433]  in
                        (FStar_Syntax_Util.t_true, uu____3430)  in
                      Simplified uu____3423
                  | Both  ->
                      let uu____3445 =
                        let uu____3454 =
                          let uu____3457 =
                            let uu____3458 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3458
                             in
                          [uu____3457]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3454)  in
                      Dual uu____3445
                  | Neg  -> Simplified (assertion, []))
             | uu____3471 -> Unchanged t)
  
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___0_3563  ->
      match uu___0_3563 with
      | Unchanged t -> let uu____3569 = f t  in Unchanged uu____3569
      | Simplified (t,gs) ->
          let uu____3576 = let uu____3583 = f t  in (uu____3583, gs)  in
          Simplified uu____3576
      | Dual (tn,tp,gs) ->
          let uu____3593 =
            let uu____3602 = f tn  in
            let uu____3603 = f tp  in (uu____3602, uu____3603, gs)  in
          Dual uu____3593
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3667 = f t1 t2  in Unchanged uu____3667
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3679 = let uu____3686 = f t1 t2  in (uu____3686, gs)
               in
            Simplified uu____3679
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3700 = let uu____3707 = f t1 t2  in (uu____3707, gs)
               in
            Simplified uu____3700
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3726 =
              let uu____3733 = f t1 t2  in
              (uu____3733, (FStar_List.append gs1 gs2))  in
            Simplified uu____3726
        | uu____3736 ->
            let uu____3745 = explode x  in
            (match uu____3745 with
             | (n1,p1,gs1) ->
                 let uu____3763 = explode y  in
                 (match uu____3763 with
                  | (n2,p2,gs2) ->
                      let uu____3781 =
                        let uu____3790 = f n1 n2  in
                        let uu____3791 = f p1 p2  in
                        (uu____3790, uu____3791, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3781))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd::tl ->
          let uu____3864 = comb2 (fun l  -> fun r  -> l :: r) hd acc  in
          aux tl uu____3864
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3913  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol1  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3956 =
              let uu____3957 = FStar_Syntax_Subst.compress t  in
              uu____3957.FStar_Syntax_Syntax.n  in
            match uu____3956 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol1 e t1  in
                let uu____3969 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3969 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol1 e t1  in
                let uu____3995 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3995 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4015;
                   FStar_Syntax_Syntax.vars = uu____4016;_},(p,uu____4018)::
                 (q,uu____4020)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let r1 = traverse f (flip pol1) e p  in
                let r2 =
                  let uu____4078 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol1 uu____4078 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____4092 = FStar_Syntax_Util.mk_imp l r  in
                       uu____4092.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4096;
                   FStar_Syntax_Syntax.vars = uu____4097;_},(p,uu____4099)::
                 (q,uu____4101)::[])
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
                  let uu____4159 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4159 p  in
                let r2 =
                  let uu____4161 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4161 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4168,Unchanged uu____4169) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4187 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4187.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4190 ->
                     let uu____4199 = explode r1  in
                     (match uu____4199 with
                      | (pn,pp,gs1) ->
                          let uu____4217 = explode r2  in
                          (match uu____4217 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4238 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4241 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4238
                                   uu____4241
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd,args) ->
                let r0 = traverse f pol1 e hd  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4305  ->
                       fun r  ->
                         match uu____4305 with
                         | (a,q) ->
                             let r' = traverse f pol1 e a  in
                             comb2
                               (fun a1  -> fun args1  -> (a1, q) :: args1) r'
                               r) args (tpure [])
                   in
                comb2
                  (fun hd1  ->
                     fun args1  -> FStar_Syntax_Syntax.Tm_app (hd1, args1))
                  r0 r1
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____4457 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4457 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4497  ->
                            match uu____4497 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol1) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4519 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___513_4551 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___513_4551.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___513_4551.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4519 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol1 e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4579 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4579.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4625 = traverse f pol1 e t1  in
                let uu____4630 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4630 uu____4625
            | FStar_Syntax_Syntax.Tm_match (sc,brs) ->
                let uu____4705 = traverse f pol1 e sc  in
                let uu____4710 =
                  let uu____4729 =
                    FStar_List.map
                      (fun br  ->
                         let uu____4746 = FStar_Syntax_Subst.open_branch br
                            in
                         match uu____4746 with
                         | (pat,w,exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs
                                in
                             let r = traverse f pol1 e1 exp  in
                             let uu____4773 =
                               comb1
                                 (fun exp1  ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1))
                                in
                             uu____4773 r) brs
                     in
                  comb_list uu____4729  in
                comb2
                  (fun sc1  ->
                     fun brs1  -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____4705 uu____4710
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol1 e
                (let uu___545_4859 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___545_4859.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___545_4859.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4866 =
                f pol1 e
                  (let uu___551_4870 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___551_4870.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___551_4870.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4866
          | Dual (tn,tp,gs) ->
              let rp =
                f pol1 e
                  (let uu___558_4880 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___558_4880.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___558_4880.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4881 = explode rp  in
              (match uu____4881 with
               | (uu____4890,p',gs') ->
                   Dual
                     ((let uu___565_4900 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___565_4900.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___565_4900.FStar_Syntax_Syntax.vars)
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
      (let uu____4945 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4945);
      (let uu____4970 = FStar_ST.op_Bang tacdbg  in
       if uu____4970
       then
         let uu____4994 =
           let uu____4996 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4996
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4999 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4994
           uu____4999
       else ());
      (let initial = (Prims.int_one, [])  in
       let uu____5034 =
         let uu____5043 = traverse by_tactic_interp Pos env goal  in
         match uu____5043 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____5067 -> failwith "no"  in
       match uu____5034 with
       | (t',gs) ->
           ((let uu____5096 = FStar_ST.op_Bang tacdbg  in
             if uu____5096
             then
               let uu____5120 =
                 let uu____5122 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____5122
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____5125 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____5120 uu____5125
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5180  ->
                    fun g  ->
                      match uu____5180 with
                      | (n,gs1) ->
                          let phi =
                            let uu____5229 =
                              let uu____5232 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____5233 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____5232 uu____5233  in
                            match uu____5229 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5234 =
                                  let uu____5240 =
                                    let uu____5242 =
                                      let uu____5244 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____5244
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5242
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5240)
                                   in
                                FStar_Errors.raise_error uu____5234
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5249 = FStar_ST.op_Bang tacdbg  in
                            if uu____5249
                            then
                              let uu____5273 = FStar_Util.string_of_int n  in
                              let uu____5275 =
                                let uu____5277 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____5277
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5273 uu____5275
                            else ());
                           (let label =
                              let uu____5283 =
                                let uu____5285 =
                                  FStar_Tactics_Types.get_label g  in
                                uu____5285 = ""  in
                              if uu____5283
                              then
                                let uu____5291 = FStar_Util.string_of_int n
                                   in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____5291
                              else
                                (let uu____5296 =
                                   let uu____5298 =
                                     FStar_Util.string_of_int n  in
                                   let uu____5300 =
                                     let uu____5302 =
                                       let uu____5304 =
                                         FStar_Tactics_Types.get_label g  in
                                       Prims.op_Hat uu____5304 ")"  in
                                     Prims.op_Hat " (" uu____5302  in
                                   Prims.op_Hat uu____5298 uu____5300  in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____5296)
                               in
                            let gt' =
                              FStar_TypeChecker_Util.label label
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____5310 =
                              let uu____5319 =
                                let uu____5326 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____5326, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____5319 :: gs1  in
                            ((n + Prims.int_one), uu____5310)))) s gs
                in
             let uu____5343 = s1  in
             match uu____5343 with
             | (uu____5365,gs1) ->
                 let gs2 = FStar_List.rev gs1  in
                 let uu____5400 =
                   let uu____5407 = FStar_Options.peek ()  in
                   (env, t', uu____5407)  in
                 uu____5400 :: gs2)))
  
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
          let uu____5431 =
            let uu____5436 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____5437 =
              let uu____5438 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5438]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____5436 uu____5437  in
          uu____5431 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____5466 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5466);
           (let uu____5490 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____5490 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____5511 =
                        let uu____5514 = FStar_Tactics_Types.goal_env g  in
                        let uu____5515 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____5514 uu____5515  in
                      match uu____5511 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____5518 = FStar_ST.op_Bang tacdbg  in
                            if uu____5518
                            then
                              let uu____5542 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____5542
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
                            let uu____5557 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____5557 guard))
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
          ((let uu____5580 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5580);
           (let gs =
              let uu____5607 = FStar_TypeChecker_Env.get_range env  in
              run_tactic_on_all_implicits tau.FStar_Syntax_Syntax.pos
                uu____5607 tau env imps
               in
            FStar_All.pipe_right gs
              (FStar_List.iter
                 (fun g  ->
                    let uu____5618 =
                      let uu____5621 = FStar_Tactics_Types.goal_env g  in
                      let uu____5622 = FStar_Tactics_Types.goal_type g  in
                      getprop uu____5621 uu____5622  in
                    match uu____5618 with
                    | FStar_Pervasives_Native.Some vc ->
                        ((let uu____5625 = FStar_ST.op_Bang tacdbg  in
                          if uu____5625
                          then
                            let uu____5649 =
                              FStar_Syntax_Print.term_to_string vc  in
                            FStar_Util.print1 "Synthesis left a goal: %s\n"
                              uu____5649
                          else ());
                         (let guard =
                            {
                              FStar_TypeChecker_Common.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Common.deferred = [];
                              FStar_TypeChecker_Common.univ_ineqs = ([], []);
                              FStar_TypeChecker_Common.implicits = []
                            }  in
                          let uu____5664 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____5664 guard))
                    | FStar_Pervasives_Native.None  ->
                        let uu____5665 = FStar_TypeChecker_Env.get_range env
                           in
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                            "synthesis left open goals") uu____5665))))
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      if env.FStar_TypeChecker_Env.nosynth
      then []
      else
        ((let uu____5687 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____5687);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let ps =
            FStar_Tactics_Basic.proofstate_of_goals
              tau.FStar_Syntax_Syntax.pos env [] []
             in
          let uu____5713 =
            let uu____5722 =
              FStar_Syntax_Embeddings.e_list
                FStar_Reflection_Embeddings.e_sigelt
               in
            run_tactic_on_ps tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos FStar_Syntax_Embeddings.e_unit ()
              uu____5722 tau env ps
             in
          match uu____5713 with
          | (gs,sigelts) ->
              ((let uu____5742 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____5747 =
                         let uu____5749 =
                           let uu____5752 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____5753 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____5752 uu____5753  in
                         FStar_Option.isSome uu____5749  in
                       Prims.op_Negation uu____5747) gs
                   in
                if uu____5742
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                      "splice left open goals") typ.FStar_Syntax_Syntax.pos
                else ());
               (let uu____5760 = FStar_ST.op_Bang tacdbg  in
                if uu____5760
                then
                  let uu____5784 =
                    FStar_Common.string_of_list
                      FStar_Syntax_Print.sigelt_to_string sigelts
                     in
                  FStar_Util.print1 "splice: got decls = %s\n" uu____5784
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
          ((let uu____5809 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5809);
           (let ps =
              FStar_Tactics_Basic.proofstate_of_goals
                tm.FStar_Syntax_Syntax.pos env [] []
               in
            let uu____5834 =
              run_tactic_on_ps tau.FStar_Syntax_Syntax.pos
                tm.FStar_Syntax_Syntax.pos FStar_Reflection_Embeddings.e_term
                tm FStar_Reflection_Embeddings.e_term tau env ps
               in
            match uu____5834 with | (gs,tm1) -> tm1))
  
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
            ((let uu____5872 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")
                 in
              FStar_ST.op_Colon_Equals tacdbg uu____5872);
             (let uu____5896 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None
                 in
              match uu____5896 with
              | (uvtm,uu____5915,g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ  in
                  let goal =
                    let uu____5933 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm
                       in
                    FStar_Syntax_Util.mk_squash u uu____5933  in
                  let uu____5934 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal
                     in
                  (match uu____5934 with
                   | (gs,w) ->
                       (FStar_List.iter
                          (fun g  ->
                             let uu____5955 =
                               let uu____5958 =
                                 FStar_Tactics_Types.goal_env g  in
                               let uu____5959 =
                                 FStar_Tactics_Types.goal_type g  in
                               getprop uu____5958 uu____5959  in
                             match uu____5955 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____5962 = FStar_ST.op_Bang tacdbg
                                      in
                                   if uu____5962
                                   then
                                     let uu____5986 =
                                       FStar_Syntax_Print.term_to_string vc
                                        in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____5986
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
                                   let uu____6001 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____6001 guard))
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
  