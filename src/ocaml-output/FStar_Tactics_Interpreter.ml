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
                                                                    "tc"
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    let uu____1187
                                                                    =
                                                                    let uu____1190
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
                                                                    let uu____1193
                                                                    =
                                                                    let uu____1196
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1201
                                                                    ->
                                                                    fun
                                                                    uu____1202
                                                                    ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu____1206
                                                                    =
                                                                    let uu____1209
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
                                                                    let uu____1214
                                                                    =
                                                                    let uu____1217
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
                                                                    let uu____1222
                                                                    =
                                                                    let uu____1225
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
                                                                    let uu____1230
                                                                    =
                                                                    let uu____1233
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
                                                                    let uu____1238
                                                                    =
                                                                    let uu____1241
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
                                                                    let uu____1246
                                                                    =
                                                                    let uu____1249
                                                                    =
                                                                    let uu____1250
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____1255
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "t_pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1250
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1255
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1266
                                                                    =
                                                                    let uu____1269
                                                                    =
                                                                    let uu____1270
                                                                    =
                                                                    let uu____1283
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1283 in
                                                                    let uu____1297
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____1302
                                                                    =
                                                                    let uu____1315
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1315 in
                                                                    let uu____1329
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1270
                                                                    uu____1297
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1302
                                                                    uu____1329
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1360
                                                                    =
                                                                    let uu____1363
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
                                                                    let uu____1366
                                                                    =
                                                                    let uu____1369
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
                                                                    let uu____1372
                                                                    =
                                                                    let uu____1375
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
                                                                    let uu____1378
                                                                    =
                                                                    let uu____1381
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
                                                                    let uu____1384
                                                                    =
                                                                    let uu____1387
                                                                    =
                                                                    let uu____1388
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    let uu____1395
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1388
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1395 in
                                                                    let uu____1412
                                                                    =
                                                                    let uu____1415
                                                                    =
                                                                    let uu____1416
                                                                    =
                                                                    let uu____1425
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1425 in
                                                                    let uu____1436
                                                                    =
                                                                    let uu____1445
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1445 in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1416
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1436 in
                                                                    let uu____1470
                                                                    =
                                                                    let uu____1473
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
                                                                    let uu____1476
                                                                    =
                                                                    let uu____1479
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
                                                                    let uu____1482
                                                                    =
                                                                    let uu____1485
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
                                                                    let uu____1488
                                                                    =
                                                                    let uu____1491
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
                                                                    let uu____1494
                                                                    =
                                                                    let uu____1497
                                                                    =
                                                                    let uu____1498
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    let uu____1503
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1498
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1503
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    let uu____1514
                                                                    =
                                                                    let uu____1517
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
                                                                    let uu____1522
                                                                    =
                                                                    let uu____1525
                                                                    =
                                                                    let uu____1526
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string in
                                                                    let uu____1533
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1526
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1533
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    let uu____1554
                                                                    =
                                                                    let uu____1557
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
                                                                    let uu____1562
                                                                    =
                                                                    let uu____1565
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
                                                                    let uu____1568
                                                                    =
                                                                    let uu____1571
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
                                                                    let uu____1574
                                                                    =
                                                                    let uu____1577
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
                                                                    let uu____1580
                                                                    =
                                                                    let uu____1583
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
                                                                    let uu____1588
                                                                    =
                                                                    let uu____1591
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1598
                                                                    ->
                                                                    fun
                                                                    uu____1599
                                                                    ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu____1602
                                                                    =
                                                                    let uu____1605
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
                                                                    uu____1613
                                                                    ->
                                                                    fun
                                                                    uu____1614
                                                                    ->
                                                                    fun
                                                                    uu____1615
                                                                    ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    [uu____1605] in
                                                                    uu____1591
                                                                    ::
                                                                    uu____1602 in
                                                                    uu____1583
                                                                    ::
                                                                    uu____1588 in
                                                                    uu____1577
                                                                    ::
                                                                    uu____1580 in
                                                                    uu____1571
                                                                    ::
                                                                    uu____1574 in
                                                                    uu____1565
                                                                    ::
                                                                    uu____1568 in
                                                                    uu____1557
                                                                    ::
                                                                    uu____1562 in
                                                                    uu____1525
                                                                    ::
                                                                    uu____1554 in
                                                                    uu____1517
                                                                    ::
                                                                    uu____1522 in
                                                                    uu____1497
                                                                    ::
                                                                    uu____1514 in
                                                                    uu____1491
                                                                    ::
                                                                    uu____1494 in
                                                                    uu____1485
                                                                    ::
                                                                    uu____1488 in
                                                                    uu____1479
                                                                    ::
                                                                    uu____1482 in
                                                                    uu____1473
                                                                    ::
                                                                    uu____1476 in
                                                                    uu____1415
                                                                    ::
                                                                    uu____1470 in
                                                                    uu____1387
                                                                    ::
                                                                    uu____1412 in
                                                                    uu____1381
                                                                    ::
                                                                    uu____1384 in
                                                                    uu____1375
                                                                    ::
                                                                    uu____1378 in
                                                                    uu____1369
                                                                    ::
                                                                    uu____1372 in
                                                                    uu____1363
                                                                    ::
                                                                    uu____1366 in
                                                                    uu____1269
                                                                    ::
                                                                    uu____1360 in
                                                                    uu____1249
                                                                    ::
                                                                    uu____1266 in
                                                                    uu____1241
                                                                    ::
                                                                    uu____1246 in
                                                                    uu____1233
                                                                    ::
                                                                    uu____1238 in
                                                                    uu____1225
                                                                    ::
                                                                    uu____1230 in
                                                                    uu____1217
                                                                    ::
                                                                    uu____1222 in
                                                                    uu____1209
                                                                    ::
                                                                    uu____1214 in
                                                                    uu____1196
                                                                    ::
                                                                    uu____1206 in
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
    let uu____1618 =
      let uu____1621 = FStar_Tactics_InterpFuns.native_tactics_steps () in
      FStar_List.append FStar_Reflection_Interpreter.reflection_primops
        uu____1621 in
    FStar_List.append uu____705 uu____1618
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
              let uu____1639 =
                let uu____1644 =
                  let uu____1645 = FStar_Syntax_Syntax.as_arg x_tm in
                  [uu____1645] in
                FStar_Syntax_Syntax.mk_Tm_app f uu____1644 in
              uu____1639 FStar_Pervasives_Native.None rng in
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
               let uu____1697 =
                 let uu____1702 =
                   let uu____1703 =
                     let uu____1712 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb in
                     FStar_Syntax_Syntax.as_arg uu____1712 in
                   [uu____1703] in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1702 in
               uu____1697 FStar_Pervasives_Native.None rng in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe] in
             let norm_f =
               let uu____1753 = FStar_Options.tactics_nbe () in
               if uu____1753
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____1776 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____1776)
             else ();
             (let result =
                let uu____1782 = primitive_steps () in
                norm_f uu____1782 steps
                  proof_state.FStar_Tactics_Types.main_context tm in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____1787 = FStar_Syntax_Print.term_to_string result in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____1787)
              else ();
              (let res =
                 let uu____1797 = FStar_Tactics_Embedding.e_result eb in
                 FStar_Tactics_InterpFuns.unembed uu____1797 result ncb in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b, ps)) ->
                   let uu____1810 = FStar_Tactics_Basic.set ps in
                   FStar_Tactics_Basic.bind uu____1810
                     (fun uu____1814 -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (e, ps)) ->
                   let uu____1819 = FStar_Tactics_Basic.set ps in
                   FStar_Tactics_Basic.bind uu____1819
                     (fun uu____1823 -> FStar_Tactics_Basic.traise e)
               | FStar_Pervasives_Native.None ->
                   let uu____1826 =
                     let uu____1832 =
                       let uu____1834 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____1834 in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____1832) in
                   FStar_Errors.raise_error uu____1826
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
              let uu____1851 =
                let uu____1852 = FStar_TypeChecker_NBETerm.as_arg x_tm in
                [uu____1852] in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1851 in
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
               let uu____1878 =
                 let uu____1879 =
                   let uu____1884 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state in
                   FStar_TypeChecker_NBETerm.as_arg uu____1884 in
                 [uu____1879] in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1878 in
             let res =
               let uu____1898 = FStar_Tactics_Embedding.e_result_nbe eb in
               FStar_TypeChecker_NBETerm.unembed uu____1898 cb result in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b, ps)) ->
                 let uu____1911 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____1911
                   (fun uu____1915 -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e, ps)) ->
                 let uu____1920 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____1920
                   (fun uu____1924 -> FStar_Tactics_Basic.traise e)
             | FStar_Pervasives_Native.None ->
                 let uu____1927 =
                   let uu____1933 =
                     let uu____1935 =
                       FStar_TypeChecker_NBETerm.t_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1935 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1933) in
                 FStar_Errors.raise_error uu____1927
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
                 let uu____1965 =
                   let uu____1970 =
                     let uu____1971 = FStar_Syntax_Syntax.as_arg x_tm in
                     [uu____1971] in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1970 in
                 uu____1965 FStar_Pervasives_Native.None rng in
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
      let em uu____2028 uu____2029 uu____2030 uu____2031 =
        failwith "Impossible: embedding tactic (1)?" in
      let un t0 w n1 =
        let uu____2080 = unembed_tactic_1_alt ea er t0 n1 in
        match uu____2080 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x ->
                  let uu____2120 = f x in FStar_Tactics_Basic.run uu____2120))
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      let uu____2136 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings.mk_emb em un uu____2136
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng ->
    fun is ->
      let errs =
        FStar_List.map
          (fun imp ->
             let uu____2176 =
               let uu____2178 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____2180 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2178 uu____2180 imp.FStar_TypeChecker_Env.imp_reason in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2176, rng)) is in
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
            (let uu____2224 = FStar_ST.op_Bang tacdbg in
             if uu____2224
             then
               let uu____2248 = FStar_Syntax_Print.term_to_string tactic in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____2248
             else ());
            (let uu____2253 = FStar_TypeChecker_TcTerm.tc_tactic env tactic in
             match uu____2253 with
             | (uu____2266, uu____2267, g) ->
                 ((let uu____2270 = FStar_ST.op_Bang tacdbg in
                   if uu____2270 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_1 FStar_Syntax_Embeddings.e_unit
                       FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb in
                   let uu____2306 =
                     FStar_TypeChecker_Env.clear_expected_typ env in
                   match uu____2306 with
                   | (env1, uu____2320) ->
                       let env2 =
                         let uu___193_2326 = env1 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___193_2326.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___193_2326.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___193_2326.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___193_2326.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___193_2326.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___193_2326.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___193_2326.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___193_2326.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___193_2326.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___193_2326.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___193_2326.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___193_2326.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___193_2326.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___193_2326.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___193_2326.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___193_2326.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___193_2326.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___193_2326.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___193_2326.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___193_2326.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___193_2326.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___193_2326.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___193_2326.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___193_2326.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___193_2326.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___193_2326.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___193_2326.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___193_2326.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___193_2326.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___193_2326.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___193_2326.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___193_2326.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___193_2326.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___193_2326.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___193_2326.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___193_2326.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___193_2326.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___193_2326.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___193_2326.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___193_2326.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___193_2326.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___193_2326.FStar_TypeChecker_Env.nbe)
                         } in
                       let env3 =
                         let uu___196_2329 = env2 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___196_2329.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___196_2329.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___196_2329.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___196_2329.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___196_2329.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___196_2329.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___196_2329.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___196_2329.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___196_2329.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___196_2329.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___196_2329.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___196_2329.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___196_2329.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___196_2329.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___196_2329.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___196_2329.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___196_2329.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___196_2329.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___196_2329.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___196_2329.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___196_2329.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___196_2329.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___196_2329.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___196_2329.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___196_2329.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___196_2329.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___196_2329.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___196_2329.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___196_2329.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___196_2329.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___196_2329.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___196_2329.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___196_2329.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___196_2329.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___196_2329.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___196_2329.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___196_2329.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___196_2329.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___196_2329.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___196_2329.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___196_2329.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___196_2329.FStar_TypeChecker_Env.nbe)
                         } in
                       let env4 =
                         let uu___199_2332 = env3 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___199_2332.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___199_2332.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___199_2332.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___199_2332.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___199_2332.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___199_2332.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___199_2332.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___199_2332.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___199_2332.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___199_2332.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___199_2332.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___199_2332.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___199_2332.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___199_2332.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___199_2332.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___199_2332.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___199_2332.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___199_2332.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___199_2332.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___199_2332.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___199_2332.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___199_2332.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___199_2332.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___199_2332.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___199_2332.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___199_2332.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___199_2332.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___199_2332.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___199_2332.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___199_2332.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___199_2332.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___199_2332.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___199_2332.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___199_2332.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___199_2332.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___199_2332.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___199_2332.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___199_2332.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___199_2332.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___199_2332.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___199_2332.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___199_2332.FStar_TypeChecker_Env.nbe)
                         } in
                       let rng =
                         let uu____2335 = FStar_Range.use_range rng_goal in
                         let uu____2336 = FStar_Range.use_range rng_tac in
                         FStar_Range.range_of_rng uu____2335 uu____2336 in
                       let uu____2337 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ in
                       (match uu____2337 with
                        | (ps, w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____2375 = FStar_ST.op_Bang tacdbg in
                              if uu____2375
                              then
                                let uu____2399 =
                                  FStar_Syntax_Print.term_to_string typ in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____2399
                              else ());
                             (let uu____2404 =
                                FStar_Util.record_time
                                  (fun uu____2416 ->
                                     let uu____2417 = tau () in
                                     FStar_Tactics_Basic.run_safe uu____2417
                                       ps) in
                              match uu____2404 with
                              | (res, ms) ->
                                  ((let uu____2435 = FStar_ST.op_Bang tacdbg in
                                    if uu____2435
                                    then FStar_Util.print_string "}\n"
                                    else ());
                                   (let uu____2463 =
                                      (FStar_ST.op_Bang tacdbg) ||
                                        (FStar_Options.tactics_info ()) in
                                    if uu____2463
                                    then
                                      let uu____2487 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic in
                                      let uu____2489 =
                                        FStar_Util.string_of_int ms in
                                      let uu____2491 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule in
                                      FStar_Util.print3
                                        "Tactic %s ran in %s ms (%s)\n"
                                        uu____2487 uu____2489 uu____2491
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____2502, ps1) ->
                                        ((let uu____2505 =
                                            FStar_ST.op_Bang tacdbg in
                                          if uu____2505
                                          then
                                            let uu____2529 =
                                              FStar_Syntax_Print.term_to_string
                                                w in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____2529
                                          else ());
                                         FStar_List.iter
                                           (fun g1 ->
                                              let uu____2539 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1 in
                                              if uu____2539
                                              then
                                                let uu____2542 =
                                                  let uu____2544 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1 in
                                                  let uu____2545 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1 in
                                                  FStar_TypeChecker_Rel.teq_nosmt_force
                                                    uu____2544 uu____2545
                                                    FStar_Syntax_Util.exp_unit in
                                                (if uu____2542
                                                 then ()
                                                 else
                                                   (let uu____2549 =
                                                      let uu____2551 =
                                                        let uu____2553 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1 in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____2553 in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____2551 in
                                                    failwith uu____2549))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____2558 =
                                            FStar_ST.op_Bang tacdbg in
                                          if uu____2558
                                          then
                                            let uu____2582 =
                                              FStar_Common.string_of_list
                                                (fun imp ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____2582
                                          else ());
                                         (let g1 =
                                            let uu___230_2590 =
                                              FStar_TypeChecker_Env.trivial_guard in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___230_2590.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___230_2590.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___230_2590.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            } in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1 in
                                          (let uu____2593 =
                                             FStar_ST.op_Bang tacdbg in
                                           if uu____2593
                                           then
                                             let uu____2617 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits) in
                                             let uu____2619 =
                                               FStar_Common.string_of_list
                                                 (fun imp ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____2617 uu____2619
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2 in
                                           (let uu____2628 =
                                              FStar_ST.op_Bang tacdbg in
                                            if uu____2628
                                            then
                                              let uu____2652 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits) in
                                              let uu____2654 =
                                                FStar_Common.string_of_list
                                                  (fun imp ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____2652 uu____2654
                                            else ());
                                           report_implicits rng_goal
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____2663 =
                                              FStar_ST.op_Bang tacdbg in
                                            if uu____2663
                                            then
                                              let uu____2687 =
                                                let uu____2688 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____2688 ps1 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____2687
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (e, ps1) ->
                                        ((let uu____2697 =
                                            let uu____2698 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____2698 ps1 in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____2697
                                            "at the time of failure");
                                         (let texn_to_string e1 =
                                            match e1 with
                                            | FStar_Tactics_Types.TacticFailure
                                                s -> s
                                            | FStar_Tactics_Types.EExn t ->
                                                let uu____2711 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t in
                                                Prims.op_Hat
                                                  "uncaught exception: "
                                                  uu____2711
                                            | e2 -> FStar_Exn.raise e2 in
                                          let uu____2716 =
                                            let uu____2722 =
                                              let uu____2724 =
                                                texn_to_string e in
                                              FStar_Util.format1
                                                "user tactic failed: %s"
                                                uu____2724 in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____2722) in
                                          FStar_Errors.raise_error uu____2716
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee -> match projectee with | Pos -> true | uu____2743 -> false
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee -> match projectee with | Neg -> true | uu____2754 -> false
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee -> match projectee with | Both -> true | uu____2765 -> false
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Unchanged _0 -> true | uu____2824 -> false
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee -> match projectee with | Unchanged _0 -> _0
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Simplified _0 -> true | uu____2868 -> false
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee -> match projectee with | Simplified _0 -> _0
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Dual _0 -> true | uu____2926 -> false
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee -> match projectee with | Dual _0 -> _0
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____2969 . 'Auu____2969 -> 'Auu____2969 tres_m =
  fun x -> Unchanged x
let (flip : pol -> pol) =
  fun p -> match p with | Pos -> Neg | Neg -> Pos | Both -> Both
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol ->
    fun e ->
      fun t ->
        let uu____2999 = FStar_Syntax_Util.head_and_args t in
        match uu____2999 with
        | (hd1, args) ->
            let uu____3042 =
              let uu____3057 =
                let uu____3058 = FStar_Syntax_Util.un_uinst hd1 in
                uu____3058.FStar_Syntax_Syntax.n in
              (uu____3057, args) in
            (match uu____3042 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (rett, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____3073))::(tactic,
                                                              FStar_Pervasives_Native.None)::
                (assertion, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos ->
                      let uu____3137 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion in
                      (match uu____3137 with
                       | (gs, uu____3145) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both ->
                      let uu____3152 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion in
                      (match uu____3152 with
                       | (gs, uu____3160) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (assertion, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos ->
                      let uu____3203 =
                        let uu____3210 =
                          let uu____3213 =
                            let uu____3214 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3214 in
                          [uu____3213] in
                        (FStar_Syntax_Util.t_true, uu____3210) in
                      Simplified uu____3203
                  | Both ->
                      let uu____3225 =
                        let uu____3234 =
                          let uu____3237 =
                            let uu____3238 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3238 in
                          [uu____3237] in
                        (assertion, FStar_Syntax_Util.t_true, uu____3234) in
                      Dual uu____3225
                  | Neg -> Simplified (assertion, []))
             | uu____3251 -> Unchanged t)
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1, gs) -> (t1, t1, gs)
    | Dual (tn, tp, gs) -> (tn, tp, gs)
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f ->
    fun uu___0_3343 ->
      match uu___0_3343 with
      | Unchanged t -> let uu____3349 = f t in Unchanged uu____3349
      | Simplified (t, gs) ->
          let uu____3356 = let uu____3363 = f t in (uu____3363, gs) in
          Simplified uu____3356
      | Dual (tn, tp, gs) ->
          let uu____3373 =
            let uu____3382 = f tn in
            let uu____3383 = f tp in (uu____3382, uu____3383, gs) in
          Dual uu____3373
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f ->
    fun x ->
      fun y ->
        match (x, y) with
        | (Unchanged t1, Unchanged t2) ->
            let uu____3447 = f t1 t2 in Unchanged uu____3447
        | (Unchanged t1, Simplified (t2, gs)) ->
            let uu____3459 = let uu____3466 = f t1 t2 in (uu____3466, gs) in
            Simplified uu____3459
        | (Simplified (t1, gs), Unchanged t2) ->
            let uu____3480 = let uu____3487 = f t1 t2 in (uu____3487, gs) in
            Simplified uu____3480
        | (Simplified (t1, gs1), Simplified (t2, gs2)) ->
            let uu____3506 =
              let uu____3513 = f t1 t2 in
              (uu____3513, (FStar_List.append gs1 gs2)) in
            Simplified uu____3506
        | uu____3516 ->
            let uu____3525 = explode x in
            (match uu____3525 with
             | (n1, p1, gs1) ->
                 let uu____3543 = explode y in
                 (match uu____3543 with
                  | (n2, p2, gs2) ->
                      let uu____3561 =
                        let uu____3570 = f n1 n2 in
                        let uu____3571 = f p1 p2 in
                        (uu____3570, uu____3571, (FStar_List.append gs1 gs2)) in
                      Dual uu____3561))
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3644 = comb2 (fun l -> fun r -> l :: r) hd1 acc in
          aux tl1 uu____3644 in
    aux (FStar_List.rev rs) (tpure [])
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs ->
    fun m -> comb2 (fun uu____3693 -> fun x -> x) (Simplified ((), gs)) m
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f ->
    fun pol ->
      fun e ->
        fun t ->
          let r =
            let uu____3736 =
              let uu____3737 = FStar_Syntax_Subst.compress t in
              uu____3737.FStar_Syntax_Syntax.n in
            match uu____3736 with
            | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
                let tr = traverse f pol e t1 in
                let uu____3749 =
                  comb1 (fun t' -> FStar_Syntax_Syntax.Tm_uinst (t', us)) in
                uu____3749 tr
            | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
                let tr = traverse f pol e t1 in
                let uu____3775 =
                  comb1 (fun t' -> FStar_Syntax_Syntax.Tm_meta (t', m)) in
                uu____3775 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3795;
                   FStar_Syntax_Syntax.vars = uu____3796;_},
                 (p, uu____3798)::(q, uu____3800)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let r1 = traverse f (flip pol) e p in
                let r2 =
                  let uu____3858 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f pol uu____3858 q in
                comb2
                  (fun l ->
                     fun r ->
                       let uu____3872 = FStar_Syntax_Util.mk_imp l r in
                       uu____3872.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3876;
                   FStar_Syntax_Syntax.vars = uu____3877;_},
                 (p, uu____3879)::(q, uu____3881)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let xq =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q in
                let r1 =
                  let uu____3939 = FStar_TypeChecker_Env.push_bv e xq in
                  traverse f Both uu____3939 p in
                let r2 =
                  let uu____3941 = FStar_TypeChecker_Env.push_bv e xp in
                  traverse f Both uu____3941 q in
                (match (r1, r2) with
                 | (Unchanged uu____3948, Unchanged uu____3949) ->
                     comb2
                       (fun l ->
                          fun r ->
                            let uu____3967 = FStar_Syntax_Util.mk_iff l r in
                            uu____3967.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3970 ->
                     let uu____3979 = explode r1 in
                     (match uu____3979 with
                      | (pn, pp, gs1) ->
                          let uu____3997 = explode r2 in
                          (match uu____3997 with
                           | (qn, qp, gs2) ->
                               let t1 =
                                 let uu____4018 =
                                   FStar_Syntax_Util.mk_imp pn qp in
                                 let uu____4021 =
                                   FStar_Syntax_Util.mk_imp qn pp in
                                 FStar_Syntax_Util.mk_conj uu____4018
                                   uu____4021 in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
                let r0 = traverse f pol e hd1 in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4085 ->
                       fun r ->
                         match uu____4085 with
                         | (a, q) ->
                             let r' = traverse f pol e a in
                             comb2 (fun a1 -> fun args1 -> (a1, q) :: args1)
                               r' r) args (tpure []) in
                comb2
                  (fun hd2 ->
                     fun args1 -> FStar_Syntax_Syntax.Tm_app (hd2, args1)) r0
                  r1
            | FStar_Syntax_Syntax.Tm_abs (bs, t1, k) ->
                let uu____4237 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____4237 with
                 | (bs1, topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let r0 =
                       FStar_List.map
                         (fun uu____4277 ->
                            match uu____4277 with
                            | (bv, aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort in
                                let uu____4299 =
                                  comb1
                                    (fun s' ->
                                       ((let uu___493_4331 = bv in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___493_4331.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___493_4331.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq)) in
                                uu____4299 r) bs1 in
                     let rbs = comb_list r0 in
                     let rt = traverse f pol e' topen in
                     comb2
                       (fun bs2 ->
                          fun t2 ->
                            let uu____4359 = FStar_Syntax_Util.abs bs2 t2 k in
                            uu____4359.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, ef) ->
                let uu____4405 = traverse f pol e t1 in
                let uu____4410 =
                  comb1
                    (fun t2 -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef)) in
                uu____4410 uu____4405
            | FStar_Syntax_Syntax.Tm_match (sc, brs) ->
                let uu____4485 = traverse f pol e sc in
                let uu____4490 =
                  let uu____4509 =
                    FStar_List.map
                      (fun br ->
                         let uu____4526 = FStar_Syntax_Subst.open_branch br in
                         match uu____4526 with
                         | (pat, w, exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs in
                             let r = traverse f pol e1 exp in
                             let uu____4553 =
                               comb1
                                 (fun exp1 ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1)) in
                             uu____4553 r) brs in
                  comb_list uu____4509 in
                comb2
                  (fun sc1 ->
                     fun brs1 -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____4485 uu____4490
            | x -> tpure x in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___525_4639 = t in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___525_4639.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___525_4639.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn', gs) ->
              let uu____4646 =
                f pol e
                  (let uu___531_4650 = t in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___531_4650.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___531_4650.FStar_Syntax_Syntax.vars)
                   }) in
              emit gs uu____4646
          | Dual (tn, tp, gs) ->
              let rp =
                f pol e
                  (let uu___538_4660 = t in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___538_4660.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___538_4660.FStar_Syntax_Syntax.vars)
                   }) in
              let uu____4661 = explode rp in
              (match uu____4661 with
               | (uu____4670, p', gs') ->
                   Dual
                     ((let uu___545_4680 = t in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___545_4680.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___545_4680.FStar_Syntax_Syntax.vars)
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
      (let uu____4725 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____4725);
      (let uu____4750 = FStar_ST.op_Bang tacdbg in
       if uu____4750
       then
         let uu____4774 =
           let uu____4776 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____4776
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____4779 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4774
           uu____4779
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____4814 =
         let uu____4823 = traverse by_tactic_interp Pos env goal in
         match uu____4823 with
         | Unchanged t' -> (t', [])
         | Simplified (t', gs) -> (t', gs)
         | uu____4847 -> failwith "no" in
       match uu____4814 with
       | (t', gs) ->
           ((let uu____4876 = FStar_ST.op_Bang tacdbg in
             if uu____4876
             then
               let uu____4900 =
                 let uu____4902 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____4902
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____4905 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4900 uu____4905
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4960 ->
                    fun g ->
                      match uu____4960 with
                      | (n1, gs1) ->
                          let phi =
                            let uu____5009 =
                              let uu____5012 = FStar_Tactics_Types.goal_env g in
                              let uu____5013 =
                                FStar_Tactics_Types.goal_type g in
                              getprop uu____5012 uu____5013 in
                            match uu____5009 with
                            | FStar_Pervasives_Native.None ->
                                let uu____5014 =
                                  let uu____5020 =
                                    let uu____5022 =
                                      let uu____5024 =
                                        FStar_Tactics_Types.goal_type g in
                                      FStar_Syntax_Print.term_to_string
                                        uu____5024 in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5022 in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5020) in
                                FStar_Errors.raise_error uu____5014
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____5029 = FStar_ST.op_Bang tacdbg in
                            if uu____5029
                            then
                              let uu____5053 = FStar_Util.string_of_int n1 in
                              let uu____5055 =
                                let uu____5057 =
                                  FStar_Tactics_Types.goal_type g in
                                FStar_Syntax_Print.term_to_string uu____5057 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5053 uu____5055
                            else ());
                           (let label1 =
                              let uu____5063 =
                                let uu____5065 =
                                  FStar_Tactics_Types.get_label g in
                                uu____5065 = "" in
                              if uu____5063
                              then
                                let uu____5071 = FStar_Util.string_of_int n1 in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____5071
                              else
                                (let uu____5076 =
                                   let uu____5078 =
                                     FStar_Util.string_of_int n1 in
                                   let uu____5080 =
                                     let uu____5082 =
                                       let uu____5084 =
                                         FStar_Tactics_Types.get_label g in
                                       Prims.op_Hat uu____5084 ")" in
                                     Prims.op_Hat " (" uu____5082 in
                                   Prims.op_Hat uu____5078 uu____5080 in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____5076) in
                            let gt' =
                              FStar_TypeChecker_Util.label label1
                                goal.FStar_Syntax_Syntax.pos phi in
                            let uu____5090 =
                              let uu____5099 =
                                let uu____5106 =
                                  FStar_Tactics_Types.goal_env g in
                                (uu____5106, gt',
                                  (g.FStar_Tactics_Types.opts)) in
                              uu____5099 :: gs1 in
                            ((n1 + (Prims.parse_int "1")), uu____5090)))) s
                 gs in
             let uu____5123 = s1 in
             match uu____5123 with
             | (uu____5145, gs1) ->
                 let uu____5165 =
                   let uu____5172 = FStar_Options.peek () in
                   (env, t', uu____5172) in
                 uu____5165 :: gs1)))
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
          let uu____5196 =
            let uu____5201 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid in
            let uu____5202 =
              let uu____5203 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu____5203] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5201 uu____5202 in
          uu____5196 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____5231 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
            FStar_ST.op_Colon_Equals tacdbg uu____5231);
           (let uu____5255 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ in
            match uu____5255 with
            | (gs, w) ->
                (FStar_List.iter
                   (fun g ->
                      let uu____5276 =
                        let uu____5279 = FStar_Tactics_Types.goal_env g in
                        let uu____5280 = FStar_Tactics_Types.goal_type g in
                        getprop uu____5279 uu____5280 in
                      match uu____5276 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____5283 = FStar_ST.op_Bang tacdbg in
                            if uu____5283
                            then
                              let uu____5307 =
                                FStar_Syntax_Print.term_to_string vc in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____5307
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              } in
                            let uu____5322 = FStar_Tactics_Types.goal_env g in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____5322 guard))
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
        ((let uu____5344 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
          FStar_ST.op_Colon_Equals tacdbg uu____5344);
         (let typ = FStar_Syntax_Syntax.t_decls in
          let uu____5369 =
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos tau env typ in
          match uu____5369 with
          | (gs, w) ->
              ((let uu____5385 =
                  FStar_List.existsML
                    (fun g ->
                       let uu____5390 =
                         let uu____5392 =
                           let uu____5395 = FStar_Tactics_Types.goal_env g in
                           let uu____5396 = FStar_Tactics_Types.goal_type g in
                           getprop uu____5395 uu____5396 in
                         FStar_Option.isSome uu____5392 in
                       Prims.op_Negation uu____5390) gs in
                if uu____5385
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
                (let uu____5404 = FStar_ST.op_Bang tacdbg in
                 if uu____5404
                 then
                   let uu____5428 = FStar_Syntax_Print.term_to_string w1 in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____5428
                 else ());
                (let uu____5433 =
                   let uu____5438 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt in
                   FStar_Tactics_InterpFuns.unembed uu____5438 w1
                     FStar_Syntax_Embeddings.id_norm_cb in
                 match uu____5433 with
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
            ((let uu____5483 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
              FStar_ST.op_Colon_Equals tacdbg uu____5483);
             (let uu____5507 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None in
              match uu____5507 with
              | (uvtm, uu____5526, g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ in
                  let goal =
                    let uu____5544 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm in
                    FStar_Syntax_Util.mk_squash u uu____5544 in
                  let uu____5545 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal in
                  (match uu____5545 with
                   | (gs, w) ->
                       (FStar_List.iter
                          (fun g ->
                             let uu____5566 =
                               let uu____5569 =
                                 FStar_Tactics_Types.goal_env g in
                               let uu____5570 =
                                 FStar_Tactics_Types.goal_type g in
                               getprop uu____5569 uu____5570 in
                             match uu____5566 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____5573 = FStar_ST.op_Bang tacdbg in
                                   if uu____5573
                                   then
                                     let uu____5597 =
                                       FStar_Syntax_Print.term_to_string vc in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____5597
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
                                   let uu____5612 =
                                     FStar_Tactics_Types.goal_env g in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____5612 guard))
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