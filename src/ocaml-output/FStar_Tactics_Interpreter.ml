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
  fun uarity ->
    fun nm ->
      fun f ->
        fun ea ->
          fun er ->
            fun nf ->
              fun ena ->
                fun enr ->
                  let uu___9_104 =
                    FStar_Tactics_InterpFuns.mktot1 uarity nm f ea er nf ena
                      enr in
                  let uu____105 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm) in
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
let mktot2' :
  'Auu____140 'Auu____141 'Auu____142 'Auu____143 'Auu____144 'Auu____145 .
    Prims.int ->
      Prims.string ->
        ('Auu____140 -> 'Auu____141 -> 'Auu____142) ->
          'Auu____140 FStar_Syntax_Embeddings.embedding ->
            'Auu____141 FStar_Syntax_Embeddings.embedding ->
              'Auu____142 FStar_Syntax_Embeddings.embedding ->
                ('Auu____143 -> 'Auu____144 -> 'Auu____145) ->
                  'Auu____143 FStar_TypeChecker_NBETerm.embedding ->
                    'Auu____144 FStar_TypeChecker_NBETerm.embedding ->
                      'Auu____145 FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity ->
    fun nm ->
      fun f ->
        fun ea ->
          fun eb ->
            fun er ->
              fun nf ->
                fun ena ->
                  fun enb ->
                    fun enr ->
                      let uu___21_244 =
                        FStar_Tactics_InterpFuns.mktot2 uarity nm f ea eb er
                          nf ena enb enr in
                      let uu____245 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm) in
                      {
                        FStar_TypeChecker_Cfg.name = uu____245;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___21_244.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___21_244.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___21_244.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___21_244.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___21_244.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___21_244.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___21_244.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
let rec e_tactic_thunk :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er ->
    let uu____551 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____558 ->
         fun uu____559 ->
           fun uu____560 ->
             fun uu____561 ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t ->
         fun w ->
           fun cb ->
             let uu____575 =
               let uu____578 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb in
               uu____578 () in
             FStar_Pervasives_Native.Some uu____575) uu____551
and e_tactic_nbe_thunk :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er ->
    let uu____590 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb ->
         fun uu____596 ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb ->
         fun t ->
           let uu____605 =
             let uu____608 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t in
             uu____608 () in
           FStar_Pervasives_Native.Some uu____605)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____590
and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea ->
    fun er ->
      let uu____623 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____633 ->
           fun uu____634 ->
             fun uu____635 ->
               fun uu____636 -> failwith "Impossible: embedding tactic (1)?")
        (fun t ->
           fun w ->
             fun cb ->
               let uu____652 = unembed_tactic_1 ea er t cb in
               FStar_Pervasives_Native.Some uu____652) uu____623
and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea ->
    fun er ->
      let uu____670 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb ->
           fun uu____679 -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb ->
           fun t ->
             let uu____690 = unembed_tactic_nbe_1 ea er cb t in
             FStar_Pervasives_Native.Some uu____690)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____670
and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____702 ->
    let uu____705 =
      let uu____708 =
        mktot1' (Prims.parse_int "0") "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit in
      let uu____711 =
        let uu____714 =
          mktot2' (Prims.parse_int "0") "set_proofstate_range"
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Syntax_Embeddings.e_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_TypeChecker_NBETerm.e_range
            FStar_Tactics_Embedding.e_proofstate_nbe in
        let uu____717 =
          let uu____720 =
            mktot1' (Prims.parse_int "0") "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe in
          let uu____723 =
            let uu____726 =
              mktot1' (Prims.parse_int "0") "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe in
            let uu____729 =
              let uu____732 =
                let uu____733 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal in
                let uu____738 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe in
                mktot1' (Prims.parse_int "0") "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____733
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____738 in
              let uu____749 =
                let uu____752 =
                  let uu____753 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal in
                  let uu____758 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe in
                  mktot1' (Prims.parse_int "0") "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____753
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____758 in
                let uu____769 =
                  let uu____772 =
                    mktot1' (Prims.parse_int "0") "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env in
                  let uu____775 =
                    let uu____778 =
                      mktot1' (Prims.parse_int "0") "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term in
                    let uu____781 =
                      let uu____784 =
                        mktot1' (Prims.parse_int "0") "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term in
                      let uu____787 =
                        let uu____790 =
                          mktot1' (Prims.parse_int "0") "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool in
                        let uu____795 =
                          let uu____798 =
                            mktot1' (Prims.parse_int "0") "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string in
                          let uu____803 =
                            let uu____806 =
                              mktot2' (Prims.parse_int "0") "set_label"
                                FStar_Tactics_Types.set_label
                                FStar_Syntax_Embeddings.e_string
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Types.set_label
                                FStar_TypeChecker_NBETerm.e_string
                                FStar_Tactics_Embedding.e_goal_nbe
                                FStar_Tactics_Embedding.e_goal_nbe in
                            let uu____811 =
                              let uu____814 =
                                FStar_Tactics_InterpFuns.mktot2
                                  (Prims.parse_int "0") "push_binder"
                                  (fun env ->
                                     fun b ->
                                       FStar_TypeChecker_Env.push_binders env
                                         [b])
                                  FStar_Reflection_Embeddings.e_env
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Reflection_Embeddings.e_env
                                  (fun env ->
                                     fun b ->
                                       FStar_TypeChecker_Env.push_binders env
                                         [b])
                                  FStar_Reflection_NBEEmbeddings.e_env
                                  FStar_Reflection_NBEEmbeddings.e_binder
                                  FStar_Reflection_NBEEmbeddings.e_env in
                              let uu____873 =
                                let uu____876 =
                                  let uu____877 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal in
                                  let uu____882 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe in
                                  FStar_Tactics_InterpFuns.mktac1
                                    (Prims.parse_int "0") "set_goals"
                                    FStar_Tactics_Basic.set_goals uu____877
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Basic.set_goals uu____882
                                    FStar_TypeChecker_NBETerm.e_unit in
                                let uu____893 =
                                  let uu____896 =
                                    let uu____897 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Tactics_Embedding.e_goal in
                                    let uu____902 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Tactics_Embedding.e_goal_nbe in
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "set_smt_goals"
                                      FStar_Tactics_Basic.set_smt_goals
                                      uu____897
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.set_smt_goals
                                      uu____902
                                      FStar_TypeChecker_NBETerm.e_unit in
                                  let uu____913 =
                                    let uu____916 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        (Prims.parse_int "0") "trivial"
                                        FStar_Tactics_Basic.trivial
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.trivial
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit in
                                    let uu____919 =
                                      let uu____922 =
                                        let uu____923 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any in
                                        let uu____928 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any in
                                        let uu____935 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any in
                                        let uu____940 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any in
                                        FStar_Tactics_InterpFuns.mktac2
                                          (Prims.parse_int "1") "catch"
                                          (fun uu____962 ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____923 uu____928
                                          (fun uu____964 ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____935 uu____940 in
                                      let uu____965 =
                                        let uu____968 =
                                          let uu____969 =
                                            e_tactic_thunk
                                              FStar_Syntax_Embeddings.e_any in
                                          let uu____974 =
                                            FStar_Syntax_Embeddings.e_either
                                              FStar_Tactics_Embedding.e_exn
                                              FStar_Syntax_Embeddings.e_any in
                                          let uu____981 =
                                            e_tactic_nbe_thunk
                                              FStar_TypeChecker_NBETerm.e_any in
                                          let uu____986 =
                                            FStar_TypeChecker_NBETerm.e_either
                                              FStar_Tactics_Embedding.e_exn_nbe
                                              FStar_TypeChecker_NBETerm.e_any in
                                          FStar_Tactics_InterpFuns.mktac2
                                            (Prims.parse_int "1") "recover"
                                            (fun uu____1008 ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_Syntax_Embeddings.e_any
                                            uu____969 uu____974
                                            (fun uu____1010 ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_TypeChecker_NBETerm.e_any
                                            uu____981 uu____986 in
                                        let uu____1011 =
                                          let uu____1014 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              (Prims.parse_int "0") "intro"
                                              FStar_Tactics_Basic.intro
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Tactics_Basic.intro
                                              FStar_TypeChecker_NBETerm.e_unit
                                              FStar_Reflection_NBEEmbeddings.e_binder in
                                          let uu____1017 =
                                            let uu____1020 =
                                              let uu____1021 =
                                                FStar_Syntax_Embeddings.e_tuple2
                                                  FStar_Reflection_Embeddings.e_binder
                                                  FStar_Reflection_Embeddings.e_binder in
                                              let uu____1028 =
                                                FStar_TypeChecker_NBETerm.e_tuple2
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                  FStar_Reflection_NBEEmbeddings.e_binder in
                                              FStar_Tactics_InterpFuns.mktac1
                                                (Prims.parse_int "0")
                                                "intro_rec"
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_Syntax_Embeddings.e_unit
                                                uu____1021
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_TypeChecker_NBETerm.e_unit
                                                uu____1028 in
                                            let uu____1045 =
                                              let uu____1048 =
                                                let uu____1049 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step in
                                                let uu____1054 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step in
                                                FStar_Tactics_InterpFuns.mktac1
                                                  (Prims.parse_int "0")
                                                  "norm"
                                                  FStar_Tactics_Basic.norm
                                                  uu____1049
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.norm
                                                  uu____1054
                                                  FStar_TypeChecker_NBETerm.e_unit in
                                              let uu____1065 =
                                                let uu____1068 =
                                                  let uu____1069 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step in
                                                  let uu____1074 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step in
                                                  FStar_Tactics_InterpFuns.mktac3
                                                    (Prims.parse_int "0")
                                                    "norm_term_env"
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_Embeddings.e_env
                                                    uu____1069
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    uu____1074
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                let uu____1085 =
                                                  let uu____1088 =
                                                    let uu____1089 =
                                                      FStar_Syntax_Embeddings.e_list
                                                        FStar_Syntax_Embeddings.e_norm_step in
                                                    let uu____1094 =
                                                      FStar_TypeChecker_NBETerm.e_list
                                                        FStar_TypeChecker_NBETerm.e_norm_step in
                                                    FStar_Tactics_InterpFuns.mktac2
                                                      (Prims.parse_int "0")
                                                      "norm_binder_type"
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____1089
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Syntax_Embeddings.e_unit
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____1094
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                      FStar_TypeChecker_NBETerm.e_unit in
                                                  let uu____1105 =
                                                    let uu____1108 =
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
                                                        FStar_TypeChecker_NBETerm.e_unit in
                                                    let uu____1113 =
                                                      let uu____1116 =
                                                        FStar_Tactics_InterpFuns.mktac1
                                                          (Prims.parse_int "0")
                                                          "binder_retype"
                                                          FStar_Tactics_Basic.binder_retype
                                                          FStar_Reflection_Embeddings.e_binder
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_Basic.binder_retype
                                                          FStar_Reflection_NBEEmbeddings.e_binder
                                                          FStar_TypeChecker_NBETerm.e_unit in
                                                      let uu____1119 =
                                                        let uu____1122 =
                                                          FStar_Tactics_InterpFuns.mktac1
                                                            (Prims.parse_int "0")
                                                            "revert"
                                                            FStar_Tactics_Basic.revert
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Tactics_Basic.revert
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit in
                                                        let uu____1125 =
                                                          let uu____1128 =
                                                            FStar_Tactics_InterpFuns.mktac1
                                                              (Prims.parse_int "0")
                                                              "clear_top"
                                                              FStar_Tactics_Basic.clear_top
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.clear_top
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                              FStar_TypeChecker_NBETerm.e_unit in
                                                          let uu____1131 =
                                                            let uu____1134 =
                                                              FStar_Tactics_InterpFuns.mktac1
                                                                (Prims.parse_int "0")
                                                                "clear"
                                                                FStar_Tactics_Basic.clear
                                                                FStar_Reflection_Embeddings.e_binder
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_Basic.clear
                                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                                FStar_TypeChecker_NBETerm.e_unit in
                                                            let uu____1137 =
                                                              let uu____1140
                                                                =
                                                                FStar_Tactics_InterpFuns.mktac1
                                                                  (Prims.parse_int "0")
                                                                  "rewrite"
                                                                  FStar_Tactics_Basic.rewrite
                                                                  FStar_Reflection_Embeddings.e_binder
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Tactics_Basic.rewrite
                                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                                  FStar_TypeChecker_NBETerm.e_unit in
                                                              let uu____1143
                                                                =
                                                                let uu____1146
                                                                  =
                                                                  FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "refine_intro"
                                                                    FStar_Tactics_Basic.refine_intro
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.refine_intro
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                let uu____1149
                                                                  =
                                                                  let uu____1152
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
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                  let uu____1159
                                                                    =
                                                                    let uu____1162
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
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1167
                                                                    =
                                                                    let uu____1170
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "apply_lemma"
                                                                    FStar_Tactics_Basic.apply_lemma
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.apply_lemma
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1173
                                                                    =
                                                                    let uu____1176
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "set_options"
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1181
                                                                    =
                                                                    let uu____1184
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "tcc"
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_comp
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_comp in
                                                                    let uu____1187
                                                                    =
                                                                    let uu____1190
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "tc"
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    let uu____1193
                                                                    =
                                                                    let uu____1196
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "unshelve"
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1199
                                                                    =
                                                                    let uu____1202
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1207
                                                                    ->
                                                                    fun
                                                                    uu____1208
                                                                    ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu____1212
                                                                    =
                                                                    let uu____1215
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "prune"
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1220
                                                                    =
                                                                    let uu____1223
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "addns"
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1228
                                                                    =
                                                                    let uu____1231
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "print"
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1236
                                                                    =
                                                                    let uu____1239
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "debugging"
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu____1244
                                                                    =
                                                                    let uu____1247
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1252
                                                                    =
                                                                    let uu____1255
                                                                    =
                                                                    let uu____1256
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____1261
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "t_pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1256
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1261
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1272
                                                                    =
                                                                    let uu____1275
                                                                    =
                                                                    let uu____1276
                                                                    =
                                                                    let uu____1289
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1289 in
                                                                    let uu____1303
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____1308
                                                                    =
                                                                    let uu____1321
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1321 in
                                                                    let uu____1335
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1276
                                                                    uu____1303
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1308
                                                                    uu____1335
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1366
                                                                    =
                                                                    let uu____1369
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1372
                                                                    =
                                                                    let uu____1375
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1378
                                                                    =
                                                                    let uu____1381
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "tadmit_t"
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1384
                                                                    =
                                                                    let uu____1387
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "join"
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1390
                                                                    =
                                                                    let uu____1393
                                                                    =
                                                                    let uu____1394
                                                                    =
                                                                    let uu____1403
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1403 in
                                                                    let uu____1414
                                                                    =
                                                                    let uu____1423
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1423 in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1394
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1414 in
                                                                    let uu____1448
                                                                    =
                                                                    let uu____1451
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_NBEEmbeddings.e_env in
                                                                    let uu____1454
                                                                    =
                                                                    let uu____1457
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view in
                                                                    let uu____1460
                                                                    =
                                                                    let uu____1463
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    let uu____1466
                                                                    =
                                                                    let uu____1469
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    let uu____1472
                                                                    =
                                                                    let uu____1475
                                                                    =
                                                                    let uu____1476
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    let uu____1481
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1476
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1481
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    let uu____1492
                                                                    =
                                                                    let uu____1495
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
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu____1500
                                                                    =
                                                                    let uu____1503
                                                                    =
                                                                    let uu____1504
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string in
                                                                    let uu____1511
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1504
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1511
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    let uu____1532
                                                                    =
                                                                    let uu____1535
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
                                                                    FStar_Reflection_NBEEmbeddings.e_bv in
                                                                    let uu____1540
                                                                    =
                                                                    let uu____1543
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1546
                                                                    =
                                                                    let uu____1549
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe in
                                                                    let uu____1552
                                                                    =
                                                                    let uu____1555
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1558
                                                                    =
                                                                    let uu____1561
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "lax_on"
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu____1566
                                                                    =
                                                                    let uu____1569
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1576
                                                                    ->
                                                                    fun
                                                                    uu____1577
                                                                    ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu____1580
                                                                    =
                                                                    let uu____1583
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
                                                                    uu____1591
                                                                    ->
                                                                    fun
                                                                    uu____1592
                                                                    ->
                                                                    fun
                                                                    uu____1593
                                                                    ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    [uu____1583] in
                                                                    uu____1569
                                                                    ::
                                                                    uu____1580 in
                                                                    uu____1561
                                                                    ::
                                                                    uu____1566 in
                                                                    uu____1555
                                                                    ::
                                                                    uu____1558 in
                                                                    uu____1549
                                                                    ::
                                                                    uu____1552 in
                                                                    uu____1543
                                                                    ::
                                                                    uu____1546 in
                                                                    uu____1535
                                                                    ::
                                                                    uu____1540 in
                                                                    uu____1503
                                                                    ::
                                                                    uu____1532 in
                                                                    uu____1495
                                                                    ::
                                                                    uu____1500 in
                                                                    uu____1475
                                                                    ::
                                                                    uu____1492 in
                                                                    uu____1469
                                                                    ::
                                                                    uu____1472 in
                                                                    uu____1463
                                                                    ::
                                                                    uu____1466 in
                                                                    uu____1457
                                                                    ::
                                                                    uu____1460 in
                                                                    uu____1451
                                                                    ::
                                                                    uu____1454 in
                                                                    uu____1393
                                                                    ::
                                                                    uu____1448 in
                                                                    uu____1387
                                                                    ::
                                                                    uu____1390 in
                                                                    uu____1381
                                                                    ::
                                                                    uu____1384 in
                                                                    uu____1375
                                                                    ::
                                                                    uu____1378 in
                                                                    uu____1369
                                                                    ::
                                                                    uu____1372 in
                                                                    uu____1275
                                                                    ::
                                                                    uu____1366 in
                                                                    uu____1255
                                                                    ::
                                                                    uu____1272 in
                                                                    uu____1247
                                                                    ::
                                                                    uu____1252 in
                                                                    uu____1239
                                                                    ::
                                                                    uu____1244 in
                                                                    uu____1231
                                                                    ::
                                                                    uu____1236 in
                                                                    uu____1223
                                                                    ::
                                                                    uu____1228 in
                                                                    uu____1215
                                                                    ::
                                                                    uu____1220 in
                                                                    uu____1202
                                                                    ::
                                                                    uu____1212 in
                                                                    uu____1196
                                                                    ::
                                                                    uu____1199 in
                                                                    uu____1190
                                                                    ::
                                                                    uu____1193 in
                                                                    uu____1184
                                                                    ::
                                                                    uu____1187 in
                                                                    uu____1176
                                                                    ::
                                                                    uu____1181 in
                                                                    uu____1170
                                                                    ::
                                                                    uu____1173 in
                                                                    uu____1162
                                                                    ::
                                                                    uu____1167 in
                                                                  uu____1152
                                                                    ::
                                                                    uu____1159 in
                                                                uu____1146 ::
                                                                  uu____1149 in
                                                              uu____1140 ::
                                                                uu____1143 in
                                                            uu____1134 ::
                                                              uu____1137 in
                                                          uu____1128 ::
                                                            uu____1131 in
                                                        uu____1122 ::
                                                          uu____1125 in
                                                      uu____1116 ::
                                                        uu____1119 in
                                                    uu____1108 :: uu____1113 in
                                                  uu____1088 :: uu____1105 in
                                                uu____1068 :: uu____1085 in
                                              uu____1048 :: uu____1065 in
                                            uu____1020 :: uu____1045 in
                                          uu____1014 :: uu____1017 in
                                        uu____968 :: uu____1011 in
                                      uu____922 :: uu____965 in
                                    uu____916 :: uu____919 in
                                  uu____896 :: uu____913 in
                                uu____876 :: uu____893 in
                              uu____814 :: uu____873 in
                            uu____806 :: uu____811 in
                          uu____798 :: uu____803 in
                        uu____790 :: uu____795 in
                      uu____784 :: uu____787 in
                    uu____778 :: uu____781 in
                  uu____772 :: uu____775 in
                uu____752 :: uu____769 in
              uu____732 :: uu____749 in
            uu____726 :: uu____729 in
          uu____720 :: uu____723 in
        uu____714 :: uu____717 in
      uu____708 :: uu____711 in
    let uu____1596 =
      let uu____1599 = FStar_Tactics_InterpFuns.native_tactics_steps () in
      FStar_List.append FStar_Reflection_Interpreter.reflection_primops
        uu____1599 in
    FStar_List.append uu____705 uu____1596
and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            'Aa -> 'Ar FStar_Tactics_Basic.tac
  =
  fun ea ->
    fun er ->
      fun f ->
        fun ncb ->
          fun x ->
            let rng = FStar_Range.dummyRange in
            let x_tm = FStar_Tactics_InterpFuns.embed ea rng x ncb in
            let app =
              let uu____1617 =
                let uu____1622 =
                  let uu____1623 = FStar_Syntax_Syntax.as_arg x_tm in
                  [uu____1623] in
                FStar_Syntax_Syntax.mk_Tm_app f uu____1622 in
              uu____1617 FStar_Pervasives_Native.None rng in
            unembed_tactic_0 er app ncb
and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb ->
    fun embedded_tac_b ->
      fun ncb ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state ->
             let rng = embedded_tac_b.FStar_Syntax_Syntax.pos in
             let embedded_tac_b1 = FStar_Syntax_Util.mk_reify embedded_tac_b in
             let tm =
               let uu____1675 =
                 let uu____1680 =
                   let uu____1681 =
                     let uu____1690 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb in
                     FStar_Syntax_Syntax.as_arg uu____1690 in
                   [uu____1681] in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1680 in
               uu____1675 FStar_Pervasives_Native.None rng in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe] in
             let norm_f =
               let uu____1731 = FStar_Options.tactics_nbe () in
               if uu____1731
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____1754 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____1754)
             else ();
             (let result =
                let uu____1760 = primitive_steps () in
                norm_f uu____1760 steps
                  proof_state.FStar_Tactics_Types.main_context tm in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____1765 = FStar_Syntax_Print.term_to_string result in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____1765)
              else ();
              (let res =
                 let uu____1775 = FStar_Tactics_Embedding.e_result eb in
                 FStar_Tactics_InterpFuns.unembed uu____1775 result ncb in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b, ps)) ->
                   let uu____1788 = FStar_Tactics_Basic.set ps in
                   FStar_Tactics_Basic.bind uu____1788
                     (fun uu____1792 -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (e, ps)) ->
                   let uu____1797 = FStar_Tactics_Basic.set ps in
                   FStar_Tactics_Basic.bind uu____1797
                     (fun uu____1801 -> FStar_Tactics_Basic.traise e)
               | FStar_Pervasives_Native.None ->
                   let uu____1804 =
                     let uu____1810 =
                       let uu____1812 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____1812 in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____1810) in
                   FStar_Errors.raise_error uu____1804
                     (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))
and unembed_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.nbe_cbs ->
          FStar_TypeChecker_NBETerm.t -> 'Aa -> 'Ar FStar_Tactics_Basic.tac
  =
  fun ea ->
    fun er ->
      fun cb ->
        fun f ->
          fun x ->
            let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x in
            let app =
              let uu____1829 =
                let uu____1830 = FStar_TypeChecker_NBETerm.as_arg x_tm in
                [uu____1830] in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1829 in
            unembed_tactic_nbe_0 er cb app
and unembed_tactic_nbe_0 :
  'Ab .
    'Ab FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.nbe_cbs ->
        FStar_TypeChecker_NBETerm.t -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb ->
    fun cb ->
      fun embedded_tac_b ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state ->
             let result =
               let uu____1856 =
                 let uu____1857 =
                   let uu____1862 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state in
                   FStar_TypeChecker_NBETerm.as_arg uu____1862 in
                 [uu____1857] in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1856 in
             let res =
               let uu____1876 = FStar_Tactics_Embedding.e_result_nbe eb in
               FStar_TypeChecker_NBETerm.unembed uu____1876 cb result in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b, ps)) ->
                 let uu____1889 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____1889
                   (fun uu____1893 -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e, ps)) ->
                 let uu____1898 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____1898
                   (fun uu____1902 -> FStar_Tactics_Basic.traise e)
             | FStar_Pervasives_Native.None ->
                 let uu____1905 =
                   let uu____1911 =
                     let uu____1913 =
                       FStar_TypeChecker_NBETerm.t_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1913 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1911) in
                 FStar_Errors.raise_error uu____1905
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
  fun ea ->
    fun er ->
      fun f ->
        fun ncb ->
          FStar_Pervasives_Native.Some
            (fun x ->
               let rng = FStar_Range.dummyRange in
               let x_tm = FStar_Tactics_InterpFuns.embed ea rng x ncb in
               let app =
                 let uu____1943 =
                   let uu____1948 =
                     let uu____1949 = FStar_Syntax_Syntax.as_arg x_tm in
                     [uu____1949] in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1948 in
                 uu____1943 FStar_Pervasives_Native.None rng in
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
  fun ea ->
    fun er ->
      let em uu____2006 uu____2007 uu____2008 uu____2009 =
        failwith "Impossible: embedding tactic (1)?" in
      let un t0 w n1 =
        let uu____2058 = unembed_tactic_1_alt ea er t0 n1 in
        match uu____2058 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x ->
                  let uu____2098 = f x in FStar_Tactics_Basic.run uu____2098))
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      let uu____2114 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings.mk_emb em un uu____2114
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng ->
    fun is ->
      let errs =
        FStar_List.map
          (fun imp ->
             let uu____2154 =
               let uu____2156 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____2158 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2156 uu____2158 imp.FStar_TypeChecker_Env.imp_reason in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2154, rng)) is in
      FStar_Errors.add_errors errs; FStar_Errors.stop_if_err ()
let (run_tactic_on_typ :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.typ ->
            (FStar_Tactics_Types.goal Prims.list * FStar_Syntax_Syntax.term))
  =
  fun rng_tac ->
    fun rng_goal ->
      fun tactic ->
        fun env ->
          fun typ ->
            (let uu____2202 = FStar_ST.op_Bang tacdbg in
             if uu____2202
             then
               let uu____2226 = FStar_Syntax_Print.term_to_string tactic in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____2226
             else ());
            (let uu____2231 = FStar_TypeChecker_TcTerm.tc_tactic env tactic in
             match uu____2231 with
             | (uu____2244, uu____2245, g) ->
                 ((let uu____2248 = FStar_ST.op_Bang tacdbg in
                   if uu____2248 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_1 FStar_Syntax_Embeddings.e_unit
                       FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb in
                   let uu____2284 =
                     FStar_TypeChecker_Env.clear_expected_typ env in
                   match uu____2284 with
                   | (env1, uu____2298) ->
                       let env2 =
                         let uu___193_2304 = env1 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___193_2304.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___193_2304.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___193_2304.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___193_2304.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___193_2304.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___193_2304.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___193_2304.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___193_2304.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___193_2304.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___193_2304.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___193_2304.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___193_2304.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___193_2304.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___193_2304.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___193_2304.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___193_2304.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___193_2304.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___193_2304.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___193_2304.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___193_2304.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___193_2304.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___193_2304.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___193_2304.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___193_2304.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___193_2304.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___193_2304.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___193_2304.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___193_2304.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___193_2304.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___193_2304.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___193_2304.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___193_2304.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___193_2304.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___193_2304.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___193_2304.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___193_2304.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___193_2304.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___193_2304.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___193_2304.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___193_2304.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___193_2304.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___193_2304.FStar_TypeChecker_Env.nbe)
                         } in
                       let env3 =
                         let uu___196_2307 = env2 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___196_2307.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___196_2307.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___196_2307.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___196_2307.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___196_2307.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___196_2307.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___196_2307.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___196_2307.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___196_2307.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___196_2307.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___196_2307.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___196_2307.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___196_2307.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___196_2307.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___196_2307.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___196_2307.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___196_2307.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___196_2307.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___196_2307.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___196_2307.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___196_2307.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___196_2307.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___196_2307.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___196_2307.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___196_2307.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___196_2307.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___196_2307.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___196_2307.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___196_2307.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___196_2307.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___196_2307.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___196_2307.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___196_2307.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___196_2307.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___196_2307.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___196_2307.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___196_2307.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___196_2307.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___196_2307.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___196_2307.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___196_2307.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___196_2307.FStar_TypeChecker_Env.nbe)
                         } in
                       let env4 =
                         let uu___199_2310 = env3 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___199_2310.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___199_2310.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___199_2310.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___199_2310.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___199_2310.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___199_2310.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___199_2310.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___199_2310.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___199_2310.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___199_2310.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___199_2310.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___199_2310.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___199_2310.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___199_2310.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___199_2310.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___199_2310.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___199_2310.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___199_2310.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___199_2310.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___199_2310.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___199_2310.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___199_2310.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___199_2310.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___199_2310.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___199_2310.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___199_2310.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___199_2310.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___199_2310.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___199_2310.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___199_2310.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___199_2310.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___199_2310.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___199_2310.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___199_2310.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___199_2310.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___199_2310.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___199_2310.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___199_2310.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___199_2310.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___199_2310.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___199_2310.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___199_2310.FStar_TypeChecker_Env.nbe)
                         } in
                       let rng =
                         let uu____2313 = FStar_Range.use_range rng_goal in
                         let uu____2314 = FStar_Range.use_range rng_tac in
                         FStar_Range.range_of_rng uu____2313 uu____2314 in
                       let uu____2315 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ in
                       (match uu____2315 with
                        | (ps, w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____2353 = FStar_ST.op_Bang tacdbg in
                              if uu____2353
                              then
                                let uu____2377 =
                                  FStar_Syntax_Print.term_to_string typ in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____2377
                              else ());
                             (let uu____2382 =
                                FStar_Util.record_time
                                  (fun uu____2394 ->
                                     let uu____2395 = tau () in
                                     FStar_Tactics_Basic.run_safe uu____2395
                                       ps) in
                              match uu____2382 with
                              | (res, ms) ->
                                  ((let uu____2413 = FStar_ST.op_Bang tacdbg in
                                    if uu____2413
                                    then FStar_Util.print_string "}\n"
                                    else ());
                                   (let uu____2441 =
                                      (FStar_ST.op_Bang tacdbg) ||
                                        (FStar_Options.tactics_info ()) in
                                    if uu____2441
                                    then
                                      let uu____2465 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic in
                                      let uu____2467 =
                                        FStar_Util.string_of_int ms in
                                      let uu____2469 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule in
                                      FStar_Util.print3
                                        "Tactic %s ran in %s ms (%s)\n"
                                        uu____2465 uu____2467 uu____2469
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____2480, ps1) ->
                                        ((let uu____2483 =
                                            FStar_ST.op_Bang tacdbg in
                                          if uu____2483
                                          then
                                            let uu____2507 =
                                              FStar_Syntax_Print.term_to_string
                                                w in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____2507
                                          else ());
                                         FStar_List.iter
                                           (fun g1 ->
                                              let uu____2517 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1 in
                                              if uu____2517
                                              then
                                                let uu____2520 =
                                                  let uu____2522 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1 in
                                                  let uu____2523 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1 in
                                                  FStar_TypeChecker_Rel.teq_nosmt_force
                                                    uu____2522 uu____2523
                                                    FStar_Syntax_Util.exp_unit in
                                                (if uu____2520
                                                 then ()
                                                 else
                                                   (let uu____2527 =
                                                      let uu____2529 =
                                                        let uu____2531 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1 in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____2531 in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____2529 in
                                                    failwith uu____2527))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____2536 =
                                            FStar_ST.op_Bang tacdbg in
                                          if uu____2536
                                          then
                                            let uu____2560 =
                                              FStar_Common.string_of_list
                                                (fun imp ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____2560
                                          else ());
                                         (let g1 =
                                            let uu___230_2568 =
                                              FStar_TypeChecker_Env.trivial_guard in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___230_2568.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___230_2568.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___230_2568.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            } in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1 in
                                          (let uu____2571 =
                                             FStar_ST.op_Bang tacdbg in
                                           if uu____2571
                                           then
                                             let uu____2595 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits) in
                                             let uu____2597 =
                                               FStar_Common.string_of_list
                                                 (fun imp ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____2595 uu____2597
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2 in
                                           (let uu____2606 =
                                              FStar_ST.op_Bang tacdbg in
                                            if uu____2606
                                            then
                                              let uu____2630 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits) in
                                              let uu____2632 =
                                                FStar_Common.string_of_list
                                                  (fun imp ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____2630 uu____2632
                                            else ());
                                           report_implicits rng_goal
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____2641 =
                                              FStar_ST.op_Bang tacdbg in
                                            if uu____2641
                                            then
                                              let uu____2665 =
                                                let uu____2666 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____2666 ps1 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____2665
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (e, ps1) ->
                                        ((let uu____2675 =
                                            let uu____2676 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____2676 ps1 in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____2675
                                            "at the time of failure");
                                         (let texn_to_string e1 =
                                            match e1 with
                                            | FStar_Tactics_Types.TacticFailure
                                                s -> s
                                            | FStar_Tactics_Types.EExn t ->
                                                let uu____2689 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t in
                                                Prims.op_Hat
                                                  "uncaught exception: "
                                                  uu____2689
                                            | e2 -> FStar_Exn.raise e2 in
                                          let uu____2694 =
                                            let uu____2700 =
                                              let uu____2702 =
                                                texn_to_string e in
                                              FStar_Util.format1
                                                "user tactic failed: %s"
                                                uu____2702 in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____2700) in
                                          FStar_Errors.raise_error uu____2694
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee -> match projectee with | Pos -> true | uu____2721 -> false
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee -> match projectee with | Neg -> true | uu____2732 -> false
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee -> match projectee with | Both -> true | uu____2743 -> false
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Unchanged _0 -> true | uu____2802 -> false
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee -> match projectee with | Unchanged _0 -> _0
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Simplified _0 -> true | uu____2846 -> false
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee -> match projectee with | Simplified _0 -> _0
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Dual _0 -> true | uu____2904 -> false
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee -> match projectee with | Dual _0 -> _0
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____2947 . 'Auu____2947 -> 'Auu____2947 tres_m =
  fun x -> Unchanged x
let (flip : pol -> pol) =
  fun p -> match p with | Pos -> Neg | Neg -> Pos | Both -> Both
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol ->
    fun e ->
      fun t ->
        let uu____2977 = FStar_Syntax_Util.head_and_args t in
        match uu____2977 with
        | (hd1, args) ->
            let uu____3020 =
              let uu____3035 =
                let uu____3036 = FStar_Syntax_Util.un_uinst hd1 in
                uu____3036.FStar_Syntax_Syntax.n in
              (uu____3035, args) in
            (match uu____3020 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (rett, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____3051))::(tactic,
                                                              FStar_Pervasives_Native.None)::
                (assertion, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos ->
                      let uu____3115 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion in
                      (match uu____3115 with
                       | (gs, uu____3123) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both ->
                      let uu____3130 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion in
                      (match uu____3130 with
                       | (gs, uu____3138) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (assertion, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos ->
                      let uu____3181 =
                        let uu____3188 =
                          let uu____3191 =
                            let uu____3192 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3192 in
                          [uu____3191] in
                        (FStar_Syntax_Util.t_true, uu____3188) in
                      Simplified uu____3181
                  | Both ->
                      let uu____3203 =
                        let uu____3212 =
                          let uu____3215 =
                            let uu____3216 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3216 in
                          [uu____3215] in
                        (assertion, FStar_Syntax_Util.t_true, uu____3212) in
                      Dual uu____3203
                  | Neg -> Simplified (assertion, []))
             | uu____3229 -> Unchanged t)
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1, gs) -> (t1, t1, gs)
    | Dual (tn, tp, gs) -> (tn, tp, gs)
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f ->
    fun uu___0_3321 ->
      match uu___0_3321 with
      | Unchanged t -> let uu____3327 = f t in Unchanged uu____3327
      | Simplified (t, gs) ->
          let uu____3334 = let uu____3341 = f t in (uu____3341, gs) in
          Simplified uu____3334
      | Dual (tn, tp, gs) ->
          let uu____3351 =
            let uu____3360 = f tn in
            let uu____3361 = f tp in (uu____3360, uu____3361, gs) in
          Dual uu____3351
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f ->
    fun x ->
      fun y ->
        match (x, y) with
        | (Unchanged t1, Unchanged t2) ->
            let uu____3425 = f t1 t2 in Unchanged uu____3425
        | (Unchanged t1, Simplified (t2, gs)) ->
            let uu____3437 = let uu____3444 = f t1 t2 in (uu____3444, gs) in
            Simplified uu____3437
        | (Simplified (t1, gs), Unchanged t2) ->
            let uu____3458 = let uu____3465 = f t1 t2 in (uu____3465, gs) in
            Simplified uu____3458
        | (Simplified (t1, gs1), Simplified (t2, gs2)) ->
            let uu____3484 =
              let uu____3491 = f t1 t2 in
              (uu____3491, (FStar_List.append gs1 gs2)) in
            Simplified uu____3484
        | uu____3494 ->
            let uu____3503 = explode x in
            (match uu____3503 with
             | (n1, p1, gs1) ->
                 let uu____3521 = explode y in
                 (match uu____3521 with
                  | (n2, p2, gs2) ->
                      let uu____3539 =
                        let uu____3548 = f n1 n2 in
                        let uu____3549 = f p1 p2 in
                        (uu____3548, uu____3549, (FStar_List.append gs1 gs2)) in
                      Dual uu____3539))
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3622 = comb2 (fun l -> fun r -> l :: r) hd1 acc in
          aux tl1 uu____3622 in
    aux (FStar_List.rev rs) (tpure [])
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs ->
    fun m -> comb2 (fun uu____3671 -> fun x -> x) (Simplified ((), gs)) m
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f ->
    fun pol ->
      fun e ->
        fun t ->
          let r =
            let uu____3714 =
              let uu____3715 = FStar_Syntax_Subst.compress t in
              uu____3715.FStar_Syntax_Syntax.n in
            match uu____3714 with
            | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
                let tr = traverse f pol e t1 in
                let uu____3727 =
                  comb1 (fun t' -> FStar_Syntax_Syntax.Tm_uinst (t', us)) in
                uu____3727 tr
            | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
                let tr = traverse f pol e t1 in
                let uu____3753 =
                  comb1 (fun t' -> FStar_Syntax_Syntax.Tm_meta (t', m)) in
                uu____3753 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3773;
                   FStar_Syntax_Syntax.vars = uu____3774;_},
                 (p, uu____3776)::(q, uu____3778)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let r1 = traverse f (flip pol) e p in
                let r2 =
                  let uu____3836 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f pol uu____3836 q in
                comb2
                  (fun l ->
                     fun r ->
                       let uu____3850 = FStar_Syntax_Util.mk_imp l r in
                       uu____3850.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3854;
                   FStar_Syntax_Syntax.vars = uu____3855;_},
                 (p, uu____3857)::(q, uu____3859)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let xq =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q in
                let r1 =
                  let uu____3917 = FStar_TypeChecker_Env.push_bv e xq in
                  traverse f Both uu____3917 p in
                let r2 =
                  let uu____3919 = FStar_TypeChecker_Env.push_bv e xp in
                  traverse f Both uu____3919 q in
                (match (r1, r2) with
                 | (Unchanged uu____3926, Unchanged uu____3927) ->
                     comb2
                       (fun l ->
                          fun r ->
                            let uu____3945 = FStar_Syntax_Util.mk_iff l r in
                            uu____3945.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3948 ->
                     let uu____3957 = explode r1 in
                     (match uu____3957 with
                      | (pn, pp, gs1) ->
                          let uu____3975 = explode r2 in
                          (match uu____3975 with
                           | (qn, qp, gs2) ->
                               let t1 =
                                 let uu____3996 =
                                   FStar_Syntax_Util.mk_imp pn qp in
                                 let uu____3999 =
                                   FStar_Syntax_Util.mk_imp qn pp in
                                 FStar_Syntax_Util.mk_conj uu____3996
                                   uu____3999 in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
                let r0 = traverse f pol e hd1 in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4063 ->
                       fun r ->
                         match uu____4063 with
                         | (a, q) ->
                             let r' = traverse f pol e a in
                             comb2 (fun a1 -> fun args1 -> (a1, q) :: args1)
                               r' r) args (tpure []) in
                comb2
                  (fun hd2 ->
                     fun args1 -> FStar_Syntax_Syntax.Tm_app (hd2, args1)) r0
                  r1
            | FStar_Syntax_Syntax.Tm_abs (bs, t1, k) ->
                let uu____4215 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____4215 with
                 | (bs1, topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let r0 =
                       FStar_List.map
                         (fun uu____4255 ->
                            match uu____4255 with
                            | (bv, aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort in
                                let uu____4277 =
                                  comb1
                                    (fun s' ->
                                       ((let uu___493_4309 = bv in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___493_4309.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___493_4309.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq)) in
                                uu____4277 r) bs1 in
                     let rbs = comb_list r0 in
                     let rt = traverse f pol e' topen in
                     comb2
                       (fun bs2 ->
                          fun t2 ->
                            let uu____4337 = FStar_Syntax_Util.abs bs2 t2 k in
                            uu____4337.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, ef) ->
                let uu____4383 = traverse f pol e t1 in
                let uu____4388 =
                  comb1
                    (fun t2 -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef)) in
                uu____4388 uu____4383
            | FStar_Syntax_Syntax.Tm_match (sc, brs) ->
                let uu____4463 = traverse f pol e sc in
                let uu____4468 =
                  let uu____4487 =
                    FStar_List.map
                      (fun br ->
                         let uu____4504 = FStar_Syntax_Subst.open_branch br in
                         match uu____4504 with
                         | (pat, w, exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs in
                             let r = traverse f pol e1 exp in
                             let uu____4531 =
                               comb1
                                 (fun exp1 ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1)) in
                             uu____4531 r) brs in
                  comb_list uu____4487 in
                comb2
                  (fun sc1 ->
                     fun brs1 -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____4463 uu____4468
            | x -> tpure x in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___525_4617 = t in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___525_4617.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___525_4617.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn', gs) ->
              let uu____4624 =
                f pol e
                  (let uu___531_4628 = t in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___531_4628.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___531_4628.FStar_Syntax_Syntax.vars)
                   }) in
              emit gs uu____4624
          | Dual (tn, tp, gs) ->
              let rp =
                f pol e
                  (let uu___538_4638 = t in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___538_4638.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___538_4638.FStar_Syntax_Syntax.vars)
                   }) in
              let uu____4639 = explode rp in
              (match uu____4639 with
               | (uu____4648, p', gs') ->
                   Dual
                     ((let uu___545_4658 = t in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___545_4658.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___545_4658.FStar_Syntax_Syntax.vars)
                       }), p', (FStar_List.append gs gs')))
let (getprop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e ->
    fun t ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant] e t in
      FStar_Syntax_Util.un_squash tn
let (preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
        FStar_Options.optionstate) Prims.list)
  =
  fun env ->
    fun goal ->
      (let uu____4703 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____4703);
      (let uu____4728 = FStar_ST.op_Bang tacdbg in
       if uu____4728
       then
         let uu____4752 =
           let uu____4754 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____4754
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____4757 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4752
           uu____4757
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____4792 =
         let uu____4801 = traverse by_tactic_interp Pos env goal in
         match uu____4801 with
         | Unchanged t' -> (t', [])
         | Simplified (t', gs) -> (t', gs)
         | uu____4825 -> failwith "no" in
       match uu____4792 with
       | (t', gs) ->
           ((let uu____4854 = FStar_ST.op_Bang tacdbg in
             if uu____4854
             then
               let uu____4878 =
                 let uu____4880 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____4880
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____4883 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4878 uu____4883
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4938 ->
                    fun g ->
                      match uu____4938 with
                      | (n1, gs1) ->
                          let phi =
                            let uu____4987 =
                              let uu____4990 = FStar_Tactics_Types.goal_env g in
                              let uu____4991 =
                                FStar_Tactics_Types.goal_type g in
                              getprop uu____4990 uu____4991 in
                            match uu____4987 with
                            | FStar_Pervasives_Native.None ->
                                let uu____4992 =
                                  let uu____4998 =
                                    let uu____5000 =
                                      let uu____5002 =
                                        FStar_Tactics_Types.goal_type g in
                                      FStar_Syntax_Print.term_to_string
                                        uu____5002 in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5000 in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____4998) in
                                FStar_Errors.raise_error uu____4992
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____5007 = FStar_ST.op_Bang tacdbg in
                            if uu____5007
                            then
                              let uu____5031 = FStar_Util.string_of_int n1 in
                              let uu____5033 =
                                let uu____5035 =
                                  FStar_Tactics_Types.goal_type g in
                                FStar_Syntax_Print.term_to_string uu____5035 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5031 uu____5033
                            else ());
                           (let label1 =
                              let uu____5041 =
                                let uu____5043 =
                                  FStar_Tactics_Types.get_label g in
                                uu____5043 = "" in
                              if uu____5041
                              then
                                let uu____5049 = FStar_Util.string_of_int n1 in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____5049
                              else
                                (let uu____5054 =
                                   let uu____5056 =
                                     FStar_Util.string_of_int n1 in
                                   let uu____5058 =
                                     let uu____5060 =
                                       let uu____5062 =
                                         FStar_Tactics_Types.get_label g in
                                       Prims.op_Hat uu____5062 ")" in
                                     Prims.op_Hat " (" uu____5060 in
                                   Prims.op_Hat uu____5056 uu____5058 in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____5054) in
                            let gt' =
                              FStar_TypeChecker_Util.label label1
                                goal.FStar_Syntax_Syntax.pos phi in
                            let uu____5068 =
                              let uu____5077 =
                                let uu____5084 =
                                  FStar_Tactics_Types.goal_env g in
                                (uu____5084, gt',
                                  (g.FStar_Tactics_Types.opts)) in
                              uu____5077 :: gs1 in
                            ((n1 + (Prims.parse_int "1")), uu____5068)))) s
                 gs in
             let uu____5101 = s1 in
             match uu____5101 with
             | (uu____5123, gs1) ->
                 let uu____5143 =
                   let uu____5150 = FStar_Options.peek () in
                   (env, t', uu____5150) in
                 uu____5143 :: gs1)))
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun typ ->
      fun tau ->
        if env.FStar_TypeChecker_Env.nosynth
        then
          let uu____5174 =
            let uu____5179 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid in
            let uu____5180 =
              let uu____5181 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu____5181] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5179 uu____5180 in
          uu____5174 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____5209 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
            FStar_ST.op_Colon_Equals tacdbg uu____5209);
           (let uu____5233 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ in
            match uu____5233 with
            | (gs, w) ->
                (FStar_List.iter
                   (fun g ->
                      let uu____5254 =
                        let uu____5257 = FStar_Tactics_Types.goal_env g in
                        let uu____5258 = FStar_Tactics_Types.goal_type g in
                        getprop uu____5257 uu____5258 in
                      match uu____5254 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____5261 = FStar_ST.op_Bang tacdbg in
                            if uu____5261
                            then
                              let uu____5285 =
                                FStar_Syntax_Print.term_to_string vc in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____5285
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              } in
                            let uu____5300 = FStar_Tactics_Types.goal_env g in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____5300 guard))
                      | FStar_Pervasives_Native.None ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                              "synthesis left open goals")
                            typ.FStar_Syntax_Syntax.pos) gs;
                 w)))
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env ->
    fun tau ->
      if env.FStar_TypeChecker_Env.nosynth
      then []
      else
        ((let uu____5322 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
          FStar_ST.op_Colon_Equals tacdbg uu____5322);
         (let typ = FStar_Syntax_Syntax.t_decls in
          let uu____5347 =
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos tau env typ in
          match uu____5347 with
          | (gs, w) ->
              ((let uu____5363 =
                  FStar_List.existsML
                    (fun g ->
                       let uu____5368 =
                         let uu____5370 =
                           let uu____5373 = FStar_Tactics_Types.goal_env g in
                           let uu____5374 = FStar_Tactics_Types.goal_type g in
                           getprop uu____5373 uu____5374 in
                         FStar_Option.isSome uu____5370 in
                       Prims.op_Negation uu____5368) gs in
                if uu____5363
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
                    FStar_TypeChecker_Env.Unmeta] env w in
                (let uu____5382 = FStar_ST.op_Bang tacdbg in
                 if uu____5382
                 then
                   let uu____5406 = FStar_Syntax_Print.term_to_string w1 in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____5406
                 else ());
                (let uu____5411 =
                   let uu____5416 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt in
                   FStar_Tactics_InterpFuns.unembed uu____5416 w1
                     FStar_Syntax_Embeddings.id_norm_cb in
                 match uu____5411 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None ->
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
  fun env ->
    fun tau ->
      fun typ ->
        fun tm ->
          if env.FStar_TypeChecker_Env.nosynth
          then tm
          else
            ((let uu____5461 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
              FStar_ST.op_Colon_Equals tacdbg uu____5461);
             (let uu____5485 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None in
              match uu____5485 with
              | (uvtm, uu____5504, g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ in
                  let goal =
                    let uu____5522 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm in
                    FStar_Syntax_Util.mk_squash u uu____5522 in
                  let uu____5523 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal in
                  (match uu____5523 with
                   | (gs, w) ->
                       (FStar_List.iter
                          (fun g ->
                             let uu____5544 =
                               let uu____5547 =
                                 FStar_Tactics_Types.goal_env g in
                               let uu____5548 =
                                 FStar_Tactics_Types.goal_type g in
                               getprop uu____5547 uu____5548 in
                             match uu____5544 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____5551 = FStar_ST.op_Bang tacdbg in
                                   if uu____5551
                                   then
                                     let uu____5575 =
                                       FStar_Syntax_Print.term_to_string vc in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____5575
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
                                     } in
                                   let uu____5590 =
                                     FStar_Tactics_Types.goal_env g in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____5590 guard))
                             | FStar_Pervasives_Native.None ->
                                 FStar_Errors.raise_error
                                   (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                                     "postprocessing left open goals")
                                   typ.FStar_Syntax_Syntax.pos) gs;
                        (let g_imp1 =
                           FStar_TypeChecker_Rel.resolve_implicits_tac env
                             g_imp in
                         report_implicits tm.FStar_Syntax_Syntax.pos
                           g_imp1.FStar_TypeChecker_Env.implicits;
                         uvtm)))))