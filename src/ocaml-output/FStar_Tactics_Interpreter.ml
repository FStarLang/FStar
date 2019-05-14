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
                  let uu___9_130 =
                    FStar_Tactics_InterpFuns.mktot1 uarity nm f ea er nf ena
                      enr
                     in
                  let uu____155 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____155;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___9_130.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___9_130.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___9_130.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___9_130.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___9_130.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___9_130.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___9_130.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot2' :
  'Auu____198 'Auu____199 'Auu____200 'Auu____201 'Auu____202 'Auu____203 .
    Prims.int ->
      Prims.string ->
        ('Auu____198 -> 'Auu____199 -> 'Auu____200) ->
          'Auu____198 FStar_Syntax_Embeddings.embedding ->
            'Auu____199 FStar_Syntax_Embeddings.embedding ->
              'Auu____200 FStar_Syntax_Embeddings.embedding ->
                ('Auu____201 -> 'Auu____202 -> 'Auu____203) ->
                  'Auu____201 FStar_TypeChecker_NBETerm.embedding ->
                    'Auu____202 FStar_TypeChecker_NBETerm.embedding ->
                      'Auu____203 FStar_TypeChecker_NBETerm.embedding ->
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
                      let uu___21_335 =
                        FStar_Tactics_InterpFuns.mktot2 uarity nm f ea eb er
                          nf ena enb enr
                         in
                      let uu____360 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm)
                         in
                      {
                        FStar_TypeChecker_Cfg.name = uu____360;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___21_335.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___21_335.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___21_335.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___21_335.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___21_335.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___21_335.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___21_335.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
  
let rec e_tactic_thunk :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____829 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____842  ->
         fun uu____843  ->
           fun uu____844  ->
             fun uu____845  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____867 =
               let uu____870 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____870 ()  in
             FStar_Pervasives_Native.Some uu____867) uu____829

and e_tactic_nbe_thunk :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____882 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____888  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____905 =
             let uu____908 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____908 ()  in
           FStar_Pervasives_Native.Some uu____905)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____882

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____923 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____939  ->
           fun uu____940  ->
             fun uu____941  ->
               fun uu____942  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____966 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____966) uu____923

and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____984 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____993  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____1012 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____1012)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____984

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____1024  ->
    let uu____1039 =
      let uu____1054 =
        mktot1' (Prims.parse_int "0") "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____1215 =
        let uu____1230 =
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
        let uu____1525 =
          let uu____1540 =
            mktot1' (Prims.parse_int "0") "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe
             in
          let uu____1835 =
            let uu____1850 =
              mktot1' (Prims.parse_int "0") "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____2145 =
              let uu____2160 =
                let uu____2185 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal
                   in
                let uu____2308 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe
                   in
                mktot1' (Prims.parse_int "0") "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____2185
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____2308
                 in
              let uu____2696 =
                let uu____2711 =
                  let uu____2736 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____2859 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mktot1' (Prims.parse_int "0") "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____2736
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____2859
                   in
                let uu____3247 =
                  let uu____3262 =
                    mktot1' (Prims.parse_int "0") "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env
                     in
                  let uu____3515 =
                    let uu____3530 =
                      mktot1' (Prims.parse_int "0") "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term
                       in
                    let uu____3683 =
                      let uu____3698 =
                        mktot1' (Prims.parse_int "0") "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____3851 =
                        let uu____3866 =
                          mktot1' (Prims.parse_int "0") "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool
                           in
                        let uu____4013 =
                          let uu____4028 =
                            mktot1' (Prims.parse_int "0") "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string
                             in
                          let uu____4175 =
                            let uu____4190 =
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
                            let uu____4455 =
                              let uu____4470 =
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
                              let uu____4917 =
                                let uu____4932 =
                                  let uu____4957 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal
                                     in
                                  let uu____5080 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe
                                     in
                                  FStar_Tactics_InterpFuns.mktac1
                                    (Prims.parse_int "0") "set_goals"
                                    FStar_Tactics_Basic.set_goals uu____4957
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Basic.set_goals uu____5080
                                    FStar_TypeChecker_NBETerm.e_unit
                                   in
                                let uu____5334 =
                                  let uu____5349 =
                                    let uu____5374 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Tactics_Embedding.e_goal
                                       in
                                    let uu____5497 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Tactics_Embedding.e_goal_nbe
                                       in
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "set_smt_goals"
                                      FStar_Tactics_Basic.set_smt_goals
                                      uu____5374
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.set_smt_goals
                                      uu____5497
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____5751 =
                                    let uu____5766 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        (Prims.parse_int "0") "trivial"
                                        FStar_Tactics_Basic.trivial
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.trivial
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____5793 =
                                      let uu____5808 =
                                        let uu____5833 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____5846 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____5861 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        let uu____5873 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        FStar_Tactics_InterpFuns.mktac2
                                          (Prims.parse_int "1") "catch"
                                          (fun uu____5914  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____5833 uu____5846
                                          (fun uu____5924  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____5861 uu____5873
                                         in
                                      let uu____5925 =
                                        let uu____5940 =
                                          let uu____5965 =
                                            e_tactic_thunk
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____5978 =
                                            FStar_Syntax_Embeddings.e_either
                                              FStar_Tactics_Embedding.e_exn
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____5993 =
                                            e_tactic_nbe_thunk
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          let uu____6005 =
                                            FStar_TypeChecker_NBETerm.e_either
                                              FStar_Tactics_Embedding.e_exn_nbe
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          FStar_Tactics_InterpFuns.mktac2
                                            (Prims.parse_int "1") "recover"
                                            (fun uu____6046  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_Syntax_Embeddings.e_any
                                            uu____5965 uu____5978
                                            (fun uu____6056  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_TypeChecker_NBETerm.e_any
                                            uu____5993 uu____6005
                                           in
                                        let uu____6057 =
                                          let uu____6072 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              (Prims.parse_int "0") "intro"
                                              FStar_Tactics_Basic.intro
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Tactics_Basic.intro
                                              FStar_TypeChecker_NBETerm.e_unit
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                             in
                                          let uu____6099 =
                                            let uu____6114 =
                                              let uu____6139 =
                                                FStar_Syntax_Embeddings.e_tuple2
                                                  FStar_Reflection_Embeddings.e_binder
                                                  FStar_Reflection_Embeddings.e_binder
                                                 in
                                              let uu____6146 =
                                                FStar_TypeChecker_NBETerm.e_tuple2
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                 in
                                              FStar_Tactics_InterpFuns.mktac1
                                                (Prims.parse_int "0")
                                                "intro_rec"
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_Syntax_Embeddings.e_unit
                                                uu____6139
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_TypeChecker_NBETerm.e_unit
                                                uu____6146
                                               in
                                            let uu____6170 =
                                              let uu____6185 =
                                                let uu____6210 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step
                                                   in
                                                let uu____6215 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step
                                                   in
                                                FStar_Tactics_InterpFuns.mktac1
                                                  (Prims.parse_int "0")
                                                  "norm"
                                                  FStar_Tactics_Basic.norm
                                                  uu____6210
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.norm
                                                  uu____6215
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                 in
                                              let uu____6233 =
                                                let uu____6248 =
                                                  let uu____6273 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step
                                                     in
                                                  let uu____6278 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step
                                                     in
                                                  FStar_Tactics_InterpFuns.mktac3
                                                    (Prims.parse_int "0")
                                                    "norm_term_env"
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_Embeddings.e_env
                                                    uu____6273
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    uu____6278
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                   in
                                                let uu____6420 =
                                                  let uu____6435 =
                                                    let uu____6460 =
                                                      FStar_Syntax_Embeddings.e_list
                                                        FStar_Syntax_Embeddings.e_norm_step
                                                       in
                                                    let uu____6465 =
                                                      FStar_TypeChecker_NBETerm.e_list
                                                        FStar_TypeChecker_NBETerm.e_norm_step
                                                       in
                                                    FStar_Tactics_InterpFuns.mktac2
                                                      (Prims.parse_int "0")
                                                      "norm_binder_type"
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____6460
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Syntax_Embeddings.e_unit
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____6465
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                      FStar_TypeChecker_NBETerm.e_unit
                                                     in
                                                  let uu____6483 =
                                                    let uu____6498 =
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
                                                    let uu____6527 =
                                                      let uu____6542 =
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
                                                      let uu____6569 =
                                                        let uu____6584 =
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
                                                        let uu____6611 =
                                                          let uu____6626 =
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
                                                          let uu____6653 =
                                                            let uu____6668 =
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
                                                            let uu____6695 =
                                                              let uu____6710
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
                                                              let uu____6737
                                                                =
                                                                let uu____6752
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
                                                                let uu____6779
                                                                  =
                                                                  let uu____6794
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
                                                                  let uu____6833
                                                                    =
                                                                    let uu____6848
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
                                                                    let uu____6885
                                                                    =
                                                                    let uu____6900
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
                                                                    let uu____6935
                                                                    =
                                                                    let uu____6950
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
                                                                    let uu____6979
                                                                    =
                                                                    let uu____6994
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "tcc"
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_comp
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_comp
                                                                     in
                                                                    let uu____7037
                                                                    =
                                                                    let uu____7052
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
                                                                    let uu____7095
                                                                    =
                                                                    let uu____7110
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
                                                                    let uu____7145
                                                                    =
                                                                    let uu____7160
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____7205
                                                                     ->
                                                                    fun
                                                                    uu____7206
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____7214
                                                                    =
                                                                    let uu____7229
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
                                                                    let uu____7258
                                                                    =
                                                                    let uu____7273
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
                                                                    let uu____7302
                                                                    =
                                                                    let uu____7317
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
                                                                    let uu____7346
                                                                    =
                                                                    let uu____7361
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
                                                                    let uu____7390
                                                                    =
                                                                    let uu____7405
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
                                                                    let uu____7434
                                                                    =
                                                                    let uu____7449
                                                                    =
                                                                    let uu____7474
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____7479
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "t_pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____7474
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____7479
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____7497
                                                                    =
                                                                    let uu____7512
                                                                    =
                                                                    let uu____7537
                                                                    =
                                                                    let uu____7554
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____7554
                                                                     in
                                                                    let uu____7572
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____7577
                                                                    =
                                                                    let uu____7601
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____7601
                                                                     in
                                                                    let uu____7626
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____7537
                                                                    uu____7572
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____7577
                                                                    uu____7626
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____7672
                                                                    =
                                                                    let uu____7687
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
                                                                    let uu____7714
                                                                    =
                                                                    let uu____7729
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
                                                                    let uu____7756
                                                                    =
                                                                    let uu____7771
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
                                                                    let uu____7806
                                                                    =
                                                                    let uu____7821
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
                                                                    let uu____7848
                                                                    =
                                                                    let uu____7863
                                                                    =
                                                                    let uu____7888
                                                                    =
                                                                    let uu____7900
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____7900
                                                                     in
                                                                    let uu____7920
                                                                    =
                                                                    let uu____7939
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____7939
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____7888
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____7920
                                                                     in
                                                                    let uu____7994
                                                                    =
                                                                    let uu____8009
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
                                                                    let uu____8144
                                                                    =
                                                                    let uu____8159
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
                                                                    let uu____8194
                                                                    =
                                                                    let uu____8209
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
                                                                    let uu____8244
                                                                    =
                                                                    let uu____8259
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
                                                                    let uu____8286
                                                                    =
                                                                    let uu____8301
                                                                    =
                                                                    let uu____8326
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____8339
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____8326
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____8339
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____8489
                                                                    =
                                                                    let uu____8504
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
                                                                    let uu____8657
                                                                    =
                                                                    let uu____8672
                                                                    =
                                                                    let uu____8697
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____8704
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____8697
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____8704
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____8732
                                                                    =
                                                                    let uu____8747
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
                                                                    let uu____8794
                                                                    =
                                                                    let uu____8809
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
                                                                    let uu____8844
                                                                    =
                                                                    let uu____8859
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
                                                                    let uu____8886
                                                                    =
                                                                    let uu____8901
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
                                                                    let uu____8928
                                                                    =
                                                                    let uu____8943
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
                                                                    let uu____8972
                                                                    =
                                                                    let uu____8987
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____9026
                                                                     ->
                                                                    fun
                                                                    uu____9027
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____9030
                                                                    =
                                                                    let uu____9045
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
                                                                    uu____9085
                                                                     ->
                                                                    fun
                                                                    uu____9086
                                                                     ->
                                                                    fun
                                                                    uu____9087
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____9045]
                                                                     in
                                                                    uu____8987
                                                                    ::
                                                                    uu____9030
                                                                     in
                                                                    uu____8943
                                                                    ::
                                                                    uu____8972
                                                                     in
                                                                    uu____8901
                                                                    ::
                                                                    uu____8928
                                                                     in
                                                                    uu____8859
                                                                    ::
                                                                    uu____8886
                                                                     in
                                                                    uu____8809
                                                                    ::
                                                                    uu____8844
                                                                     in
                                                                    uu____8747
                                                                    ::
                                                                    uu____8794
                                                                     in
                                                                    uu____8672
                                                                    ::
                                                                    uu____8732
                                                                     in
                                                                    uu____8504
                                                                    ::
                                                                    uu____8657
                                                                     in
                                                                    uu____8301
                                                                    ::
                                                                    uu____8489
                                                                     in
                                                                    uu____8259
                                                                    ::
                                                                    uu____8286
                                                                     in
                                                                    uu____8209
                                                                    ::
                                                                    uu____8244
                                                                     in
                                                                    uu____8159
                                                                    ::
                                                                    uu____8194
                                                                     in
                                                                    uu____8009
                                                                    ::
                                                                    uu____8144
                                                                     in
                                                                    uu____7863
                                                                    ::
                                                                    uu____7994
                                                                     in
                                                                    uu____7821
                                                                    ::
                                                                    uu____7848
                                                                     in
                                                                    uu____7771
                                                                    ::
                                                                    uu____7806
                                                                     in
                                                                    uu____7729
                                                                    ::
                                                                    uu____7756
                                                                     in
                                                                    uu____7687
                                                                    ::
                                                                    uu____7714
                                                                     in
                                                                    uu____7512
                                                                    ::
                                                                    uu____7672
                                                                     in
                                                                    uu____7449
                                                                    ::
                                                                    uu____7497
                                                                     in
                                                                    uu____7405
                                                                    ::
                                                                    uu____7434
                                                                     in
                                                                    uu____7361
                                                                    ::
                                                                    uu____7390
                                                                     in
                                                                    uu____7317
                                                                    ::
                                                                    uu____7346
                                                                     in
                                                                    uu____7273
                                                                    ::
                                                                    uu____7302
                                                                     in
                                                                    uu____7229
                                                                    ::
                                                                    uu____7258
                                                                     in
                                                                    uu____7160
                                                                    ::
                                                                    uu____7214
                                                                     in
                                                                    uu____7110
                                                                    ::
                                                                    uu____7145
                                                                     in
                                                                    uu____7052
                                                                    ::
                                                                    uu____7095
                                                                     in
                                                                    uu____6994
                                                                    ::
                                                                    uu____7037
                                                                     in
                                                                    uu____6950
                                                                    ::
                                                                    uu____6979
                                                                     in
                                                                    uu____6900
                                                                    ::
                                                                    uu____6935
                                                                     in
                                                                    uu____6848
                                                                    ::
                                                                    uu____6885
                                                                     in
                                                                  uu____6794
                                                                    ::
                                                                    uu____6833
                                                                   in
                                                                uu____6752 ::
                                                                  uu____6779
                                                                 in
                                                              uu____6710 ::
                                                                uu____6737
                                                               in
                                                            uu____6668 ::
                                                              uu____6695
                                                             in
                                                          uu____6626 ::
                                                            uu____6653
                                                           in
                                                        uu____6584 ::
                                                          uu____6611
                                                         in
                                                      uu____6542 ::
                                                        uu____6569
                                                       in
                                                    uu____6498 :: uu____6527
                                                     in
                                                  uu____6435 :: uu____6483
                                                   in
                                                uu____6248 :: uu____6420  in
                                              uu____6185 :: uu____6233  in
                                            uu____6114 :: uu____6170  in
                                          uu____6072 :: uu____6099  in
                                        uu____5940 :: uu____6057  in
                                      uu____5808 :: uu____5925  in
                                    uu____5766 :: uu____5793  in
                                  uu____5349 :: uu____5751  in
                                uu____4932 :: uu____5334  in
                              uu____4470 :: uu____4917  in
                            uu____4190 :: uu____4455  in
                          uu____4028 :: uu____4175  in
                        uu____3866 :: uu____4013  in
                      uu____3698 :: uu____3851  in
                    uu____3530 :: uu____3683  in
                  uu____3262 :: uu____3515  in
                uu____2711 :: uu____3247  in
              uu____2160 :: uu____2696  in
            uu____1850 :: uu____2145  in
          uu____1540 :: uu____1835  in
        uu____1230 :: uu____1525  in
      uu____1054 :: uu____1215  in
    let uu____9870 =
      let uu____9885 = FStar_Tactics_InterpFuns.native_tactics_steps ()  in
      FStar_List.append FStar_Reflection_Interpreter.reflection_primops
        uu____9885
       in
    FStar_List.append uu____1039 uu____9870

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
              let uu____9959 =
                let uu____9964 =
                  let uu____9965 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____9965]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____9964  in
              uu____9959 FStar_Pervasives_Native.None rng  in
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
               let uu____10183 =
                 let uu____10188 =
                   let uu____10189 =
                     let uu____10202 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____10202  in
                   [uu____10189]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____10188
                  in
               uu____10183 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____10400 = FStar_Options.tactics_nbe ()  in
               if uu____10400
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____10497 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____10497)
             else ();
             (let result =
                let uu____10511 = primitive_steps ()  in
                norm_f uu____10511 steps
                  proof_state.FStar_Tactics_Types.main_context tm
                 in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____10528 = FStar_Syntax_Print.term_to_string result
                    in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____10528)
              else ();
              (let res =
                 let uu____10538 = FStar_Tactics_Embedding.e_result eb  in
                 FStar_Tactics_InterpFuns.unembed uu____10538 result ncb  in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b,ps)) ->
                   let uu____10685 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____10685
                     (fun uu____10689  -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (e,ps)) ->
                   let uu____10828 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____10828
                     (fun uu____10832  -> FStar_Tactics_Basic.traise e)
               | FStar_Pervasives_Native.None  ->
                   let uu____10835 =
                     let uu____10841 =
                       let uu____10843 =
                         FStar_Syntax_Print.term_to_string result  in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____10843
                        in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____10841)  in
                   FStar_Errors.raise_error uu____10835
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
              let uu____10864 =
                let uu____10865 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____10865]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____10864  in
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
               let uu____11029 =
                 let uu____11030 =
                   let uu____11035 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____11035  in
                 [uu____11030]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b
                 uu____11029
                in
             let res =
               let uu____11116 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____11116 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____11270 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____11270
                   (fun uu____11274  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____11413 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____11413
                   (fun uu____11417  -> FStar_Tactics_Basic.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____11420 =
                   let uu____11426 =
                     let uu____11428 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____11428
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____11426)  in
                 FStar_Errors.raise_error uu____11420
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
                 let uu____11478 =
                   let uu____11483 =
                     let uu____11484 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____11484]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____11483  in
                 uu____11478 FStar_Pervasives_Native.None rng  in
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
      let em uu____11624 uu____11625 uu____11626 uu____11627 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n1 =
        let uu____11889 = unembed_tactic_1_alt ea er t0 n1  in
        match uu____11889 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____12063 = f x  in
                  FStar_Tactics_Basic.run uu____12063))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____12146 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____12146

let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____12267 =
               let uu____12269 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____12271 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____12269 uu____12271 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____12267, rng)) is
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
            (let uu____12565 = FStar_ST.op_Bang tacdbg  in
             if uu____12565
             then
               let uu____12589 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____12589
             else ());
            (let uu____12594 = FStar_TypeChecker_TcTerm.tc_tactic env tactic
                in
             match uu____12594 with
             | (uu____12686,uu____12687,g) ->
                 ((let uu____12722 = FStar_ST.op_Bang tacdbg  in
                   if uu____12722 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_1 FStar_Syntax_Embeddings.e_unit
                       FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb
                      in
                   let uu____12758 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____12758 with
                   | (env1,uu____12893) ->
                       let env2 =
                         let uu___193_13123 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___193_13123.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___193_13123.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___193_13123.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___193_13123.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___193_13123.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___193_13123.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___193_13123.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___193_13123.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___193_13123.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___193_13123.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___193_13123.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___193_13123.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___193_13123.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___193_13123.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___193_13123.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___193_13123.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___193_13123.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___193_13123.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___193_13123.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___193_13123.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___193_13123.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___193_13123.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___193_13123.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___193_13123.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___193_13123.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___193_13123.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___193_13123.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___193_13123.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___193_13123.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___193_13123.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___193_13123.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___193_13123.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___193_13123.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___193_13123.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___193_13123.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___193_13123.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___193_13123.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___193_13123.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___193_13123.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___193_13123.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___193_13123.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___193_13123.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___196_13342 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___196_13342.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___196_13342.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___196_13342.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___196_13342.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___196_13342.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___196_13342.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___196_13342.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___196_13342.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___196_13342.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___196_13342.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___196_13342.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___196_13342.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___196_13342.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___196_13342.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___196_13342.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___196_13342.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___196_13342.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___196_13342.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___196_13342.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___196_13342.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___196_13342.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___196_13342.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___196_13342.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___196_13342.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___196_13342.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___196_13342.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___196_13342.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___196_13342.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___196_13342.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___196_13342.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___196_13342.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___196_13342.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___196_13342.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___196_13342.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___196_13342.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___196_13342.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___196_13342.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___196_13342.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___196_13342.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___196_13342.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___196_13342.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___196_13342.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___199_13561 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___199_13561.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___199_13561.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___199_13561.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___199_13561.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___199_13561.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___199_13561.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___199_13561.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___199_13561.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___199_13561.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___199_13561.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___199_13561.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___199_13561.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___199_13561.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___199_13561.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___199_13561.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___199_13561.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___199_13561.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___199_13561.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___199_13561.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___199_13561.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___199_13561.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___199_13561.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___199_13561.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___199_13561.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___199_13561.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___199_13561.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___199_13561.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___199_13561.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___199_13561.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___199_13561.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___199_13561.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___199_13561.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___199_13561.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___199_13561.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___199_13561.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___199_13561.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___199_13561.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___199_13561.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___199_13561.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___199_13561.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___199_13561.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___199_13561.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____13672 = FStar_Range.use_range rng_goal  in
                         let uu____13673 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____13672 uu____13673  in
                       let uu____13674 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____13674 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____14150 = FStar_ST.op_Bang tacdbg  in
                              if uu____14150
                              then
                                let uu____14174 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____14174
                              else ());
                             (let uu____14179 =
                                FStar_Util.record_time
                                  (fun uu____14191  ->
                                     let uu____14192 = tau ()  in
                                     FStar_Tactics_Basic.run_safe uu____14192
                                       ps)
                                 in
                              match uu____14179 with
                              | (res,ms) ->
                                  ((let uu____14273 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____14273
                                    then FStar_Util.print_string "}\n"
                                    else ());
                                   (let uu____14301 =
                                      (FStar_ST.op_Bang tacdbg) ||
                                        (FStar_Options.tactics_info ())
                                       in
                                    if uu____14301
                                    then
                                      let uu____14325 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____14327 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____14329 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "Tactic %s ran in %s ms (%s)\n"
                                        uu____14325 uu____14327 uu____14329
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____14403,ps1) ->
                                        ((let uu____14540 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____14540
                                          then
                                            let uu____14564 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____14564
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____14692 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____14692
                                              then
                                                let uu____14695 =
                                                  let uu____14697 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____14806 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt_force
                                                    uu____14697 uu____14806
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____14695
                                                 then ()
                                                 else
                                                   (let uu____14818 =
                                                      let uu____14820 =
                                                        let uu____14822 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____14822
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____14820
                                                       in
                                                    failwith uu____14818))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____14894 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____14894
                                          then
                                            let uu____14918 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____14918
                                          else ());
                                         (let g1 =
                                            let uu___230_14942 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___230_14942.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___230_14942.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___230_14942.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____14961 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____14961
                                           then
                                             let uu____14985 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits)
                                                in
                                             let uu____14991 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____14985 uu____14991
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____15016 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____15016
                                            then
                                              let uu____15040 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits)
                                                 in
                                              let uu____15046 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____15040 uu____15046
                                            else ());
                                           report_implicits rng_goal
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____15063 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____15063
                                            then
                                              let uu____15087 =
                                                let uu____15222 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc
                                                   in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____15222 ps1
                                                 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____15087
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (e,ps1) ->
                                        ((let uu____15487 =
                                            let uu____15622 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____15622 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____15487
                                            "at the time of failure");
                                         (let texn_to_string e1 =
                                            match e1 with
                                            | FStar_Tactics_Types.TacticFailure
                                                s -> s
                                            | FStar_Tactics_Types.EExn t ->
                                                let uu____15639 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                Prims.op_Hat
                                                  "uncaught exception: "
                                                  uu____15639
                                            | e2 -> FStar_Exn.raise e2  in
                                          let uu____15644 =
                                            let uu____15650 =
                                              let uu____15652 =
                                                texn_to_string e  in
                                              FStar_Util.format1
                                                "user tactic failed: %s"
                                                uu____15652
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____15650)
                                             in
                                          FStar_Errors.raise_error
                                            uu____15644
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pos  -> true | uu____15734 -> false
  
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neg  -> true | uu____15745 -> false
  
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____15756 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____15933 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____16036 -> false
  
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____16271 -> false
  
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____16436 . 'Auu____16436 -> 'Auu____16436 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____16582 = FStar_Syntax_Util.head_and_args t  in
        match uu____16582 with
        | (hd1,args) ->
            let uu____16649 =
              let uu____16668 =
                let uu____16669 = FStar_Syntax_Util.un_uinst hd1  in
                uu____16669.FStar_Syntax_Syntax.n  in
              (uu____16668, args)  in
            (match uu____16649 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____16696))::(tactic,FStar_Pervasives_Native.None
                                                                  )::
                (assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____16807 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____16807 with
                       | (gs,uu____16878) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____17078 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____17078 with
                       | (gs,uu____17149) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____17538 =
                        let uu____17608 =
                          let uu____17670 =
                            let uu____17789 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____17789
                             in
                          [uu____17670]  in
                        (FStar_Syntax_Util.t_true, uu____17608)  in
                      Simplified uu____17538
                  | Both  ->
                      let uu____18233 =
                        let uu____18309 =
                          let uu____18371 =
                            let uu____18490 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____18490
                             in
                          [uu____18371]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____18309)
                         in
                      Dual uu____18233
                  | Neg  -> Simplified (assertion, []))
             | uu____19066 -> Unchanged t)
  
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___0_19756  ->
      match uu___0_19756 with
      | Unchanged t -> let uu____19762 = f t  in Unchanged uu____19762
      | Simplified (t,gs) ->
          let uu____19887 = let uu____19953 = f t  in (uu____19953, gs)  in
          Simplified uu____19887
      | Dual (tn,tp,gs) ->
          let uu____20140 =
            let uu____20208 = f tn  in
            let uu____20209 = f tp  in (uu____20208, uu____20209, gs)  in
          Dual uu____20140
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____20332 = f t1 t2  in Unchanged uu____20332
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____20462 = let uu____20528 = f t1 t2  in (uu____20528, gs)
               in
            Simplified uu____20462
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____20719 = let uu____20785 = f t1 t2  in (uu____20785, gs)
               in
            Simplified uu____20719
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____21099 =
              let uu____21165 = f t1 t2  in
              (uu____21165, (FStar_List.append gs1 gs2))  in
            Simplified uu____21099
        | uu____21286 ->
            let uu____21295 = explode x  in
            (match uu____21295 with
             | (n1,p1,gs1) ->
                 let uu____21490 = explode y  in
                 (match uu____21490 with
                  | (n2,p2,gs2) ->
                      let uu____21685 =
                        let uu____21753 = f n1 n2  in
                        let uu____21754 = f p1 p2  in
                        (uu____21753, uu____21754,
                          (FStar_List.append gs1 gs2))
                         in
                      Dual uu____21685))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____21945 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____21945
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____22112  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____22446 =
              let uu____22447 = FStar_Syntax_Subst.compress t  in
              uu____22447.FStar_Syntax_Syntax.n  in
            match uu____22446 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____22475 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____22475 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____22525 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____22525 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____22561;
                   FStar_Syntax_Syntax.vars = uu____22562;_},(p,uu____22564)::
                 (q,uu____22566)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____22677 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____22677 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____22815 = FStar_Syntax_Util.mk_imp l r  in
                       uu____22815.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____22827;
                   FStar_Syntax_Syntax.vars = uu____22828;_},(p,uu____22830)::
                 (q,uu____22832)::[])
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
                  let uu____22953 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____22953 p  in
                let r2 =
                  let uu____23063 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____23063 q  in
                (match (r1, r2) with
                 | (Unchanged uu____23186,Unchanged uu____23187) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____23245 = FStar_Syntax_Util.mk_iff l r
                               in
                            uu____23245.FStar_Syntax_Syntax.n) r1 r2
                 | uu____23256 ->
                     let uu____23273 = explode r1  in
                     (match uu____23273 with
                      | (pn,pp,gs1) ->
                          let uu____23496 = explode r2  in
                          (match uu____23496 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____23730 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____23741 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____23730
                                   uu____23741
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____23959  ->
                       fun r  ->
                         match uu____23959 with
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
                let uu____24223 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____24223 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____24398  ->
                            match uu____24398 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____24440 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___493_24499 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___493_24499.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___493_24499.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____24440 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____24555 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____24555.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____24649 = traverse f pol e t1  in
                let uu____24658 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____24658 uu____24649
            | FStar_Syntax_Syntax.Tm_match (sc,brs) ->
                let uu____24795 = traverse f pol e sc  in
                let uu____24804 =
                  let uu____24834 =
                    FStar_List.map
                      (fun br  ->
                         let uu____24851 = FStar_Syntax_Subst.open_branch br
                            in
                         match uu____24851 with
                         | (pat,w,exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs
                                in
                             let r = traverse f pol e1 exp  in
                             let uu____25013 =
                               comb1
                                 (fun exp1  ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1))
                                in
                             uu____25013 r) brs
                     in
                  comb_list uu____24834  in
                comb2
                  (fun sc1  ->
                     fun brs1  -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____24795 uu____24804
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___525_25164 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___525_25164.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___525_25164.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____25297 =
                f pol e
                  (let uu___531_25305 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___531_25305.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___531_25305.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____25297
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___538_25445 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___538_25445.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___538_25445.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____25454 = explode rp  in
              (match uu____25454 with
               | (uu____25534,p',gs') ->
                   Dual
                     ((let uu___545_25749 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___545_25749.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___545_25749.FStar_Syntax_Syntax.vars)
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
      (let uu____26225 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____26225);
      (let uu____26250 = FStar_ST.op_Bang tacdbg  in
       if uu____26250
       then
         let uu____26274 =
           let uu____26276 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____26276
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____26279 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____26274
           uu____26279
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____26488 =
         let uu____26560 = traverse by_tactic_interp Pos env goal  in
         match uu____26560 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____26970 -> failwith "no"  in
       match uu____26488 with
       | (t',gs) ->
           ((let uu____27246 = FStar_ST.op_Bang tacdbg  in
             if uu____27246
             then
               let uu____27270 =
                 let uu____27272 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____27272
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____27275 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____27270 uu____27275
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____27563  ->
                    fun g  ->
                      match uu____27563 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____27911 =
                              let uu____27918 =
                                FStar_Tactics_Types.goal_env g  in
                              let uu____28027 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____27918 uu____28027  in
                            match uu____27911 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____28044 =
                                  let uu____28050 =
                                    let uu____28052 =
                                      let uu____28054 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____28054
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____28052
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____28050)
                                   in
                                FStar_Errors.raise_error uu____28044
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____28079 = FStar_ST.op_Bang tacdbg  in
                            if uu____28079
                            then
                              let uu____28103 = FStar_Util.string_of_int n1
                                 in
                              let uu____28105 =
                                let uu____28107 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____28107
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____28103 uu____28105
                            else ());
                           (let label1 =
                              let uu____28121 =
                                let uu____28123 =
                                  FStar_Tactics_Types.get_label g  in
                                uu____28123 = ""  in
                              if uu____28121
                              then
                                let uu____28129 = FStar_Util.string_of_int n1
                                   in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____28129
                              else
                                (let uu____28134 =
                                   let uu____28136 =
                                     FStar_Util.string_of_int n1  in
                                   let uu____28138 =
                                     let uu____28140 =
                                       let uu____28142 =
                                         FStar_Tactics_Types.get_label g  in
                                       Prims.op_Hat uu____28142 ")"  in
                                     Prims.op_Hat " (" uu____28140  in
                                   Prims.op_Hat uu____28136 uu____28138  in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____28134)
                               in
                            let gt' =
                              FStar_TypeChecker_Util.label label1
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____28156 =
                              let uu____28223 =
                                let uu____28288 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____28288, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____28223 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____28156)))) s
                 gs
                in
             let uu____28587 = s1  in
             match uu____28587 with
             | (uu____28725,gs1) ->
                 let uu____28861 =
                   let uu____28926 = FStar_Options.peek ()  in
                   (env, t', uu____28926)  in
                 uu____28861 :: gs1)))
  
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
          let uu____29198 =
            let uu____29203 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____29212 =
              let uu____29213 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____29213]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____29203 uu____29212  in
          uu____29198 FStar_Pervasives_Native.None
            typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____29253 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____29253);
           (let uu____29277 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____29277 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____29609 =
                        let uu____29616 = FStar_Tactics_Types.goal_env g  in
                        let uu____29725 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____29616 uu____29725  in
                      match uu____29609 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____29744 = FStar_ST.op_Bang tacdbg  in
                            if uu____29744
                            then
                              let uu____29768 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____29768
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____29795 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____29795 guard))
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
        ((let uu____30060 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____30060);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____30093 =
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos tau env typ
             in
          match uu____30093 with
          | (gs,w) ->
              ((let uu____30303 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____30426 =
                         let uu____30428 =
                           let uu____30435 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____30544 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____30435 uu____30544  in
                         FStar_Option.isSome uu____30428  in
                       Prims.op_Negation uu____30426) gs
                   in
                if uu____30303
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
                (let uu____30572 = FStar_ST.op_Bang tacdbg  in
                 if uu____30572
                 then
                   let uu____30596 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____30596
                 else ());
                (let uu____30601 =
                   let uu____30611 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____30611 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____30601 with
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
            ((let uu____30836 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")
                 in
              FStar_ST.op_Colon_Equals tacdbg uu____30836);
             (let uu____30860 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None
                 in
              match uu____30860 with
              | (uvtm,uu____30903,g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ  in
                  let goal =
                    let uu____30961 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm
                       in
                    FStar_Syntax_Util.mk_squash u uu____30961  in
                  let uu____30970 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal
                     in
                  (match uu____30970 with
                   | (gs,w) ->
                       (FStar_List.iter
                          (fun g  ->
                             let uu____31302 =
                               let uu____31309 =
                                 FStar_Tactics_Types.goal_env g  in
                               let uu____31418 =
                                 FStar_Tactics_Types.goal_type g  in
                               getprop uu____31309 uu____31418  in
                             match uu____31302 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____31437 = FStar_ST.op_Bang tacdbg
                                      in
                                   if uu____31437
                                   then
                                     let uu____31461 =
                                       FStar_Syntax_Print.term_to_string vc
                                        in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____31461
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
                                   let uu____31488 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____31488 guard))
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
  