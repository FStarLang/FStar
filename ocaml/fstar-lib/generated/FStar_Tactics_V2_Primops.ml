open Prims
let solve : 'a . 'a -> 'a = fun ev -> ev
let (uu___2 :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V2_Embeddings.e_term
let unseal :
  'uuuuu 'a .
    'uuuuu -> 'a FStar_Compiler_Sealed.sealed -> 'a FStar_Tactics_Monad.tac
  =
  fun uu___1 ->
    fun uu___ ->
      (fun _typ ->
         fun x ->
           Obj.magic
             (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                (Obj.magic (FStar_Compiler_Sealed.unseal x)))) uu___1 uu___
let (unseal_step : FStar_TypeChecker_Primops_Base.primitive_step) =
  let s =
    FStar_Tactics_InterpFuns.mk_tac_step_2 Prims.int_one "unseal"
      FStar_Syntax_Embeddings.e_any
      (FStar_Syntax_Embeddings.e_sealed FStar_Syntax_Embeddings.e_any)
      FStar_Syntax_Embeddings.e_any FStar_TypeChecker_NBETerm.e_any
      (FStar_TypeChecker_NBETerm.e_sealed FStar_TypeChecker_NBETerm.e_any)
      FStar_TypeChecker_NBETerm.e_any unseal unseal in
  {
    FStar_TypeChecker_Primops_Base.name = FStar_Parser_Const.unseal_lid;
    FStar_TypeChecker_Primops_Base.arity =
      (s.FStar_TypeChecker_Primops_Base.arity);
    FStar_TypeChecker_Primops_Base.univ_arity =
      (s.FStar_TypeChecker_Primops_Base.univ_arity);
    FStar_TypeChecker_Primops_Base.auto_reflect =
      (s.FStar_TypeChecker_Primops_Base.auto_reflect);
    FStar_TypeChecker_Primops_Base.strong_reduction_ok =
      (s.FStar_TypeChecker_Primops_Base.strong_reduction_ok);
    FStar_TypeChecker_Primops_Base.requires_binder_substitution =
      (s.FStar_TypeChecker_Primops_Base.requires_binder_substitution);
    FStar_TypeChecker_Primops_Base.renorm_after =
      (s.FStar_TypeChecker_Primops_Base.renorm_after);
    FStar_TypeChecker_Primops_Base.interpretation =
      (s.FStar_TypeChecker_Primops_Base.interpretation);
    FStar_TypeChecker_Primops_Base.interpretation_nbe =
      (s.FStar_TypeChecker_Primops_Base.interpretation_nbe)
  }
let e_ret_t :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      ('a FStar_Pervasives_Native.option * FStar_Tactics_V2_Basic.issues)
        FStar_Syntax_Embeddings_Base.embedding
  =
  fun d ->
    solve
      (FStar_Syntax_Embeddings.e_tuple2 (FStar_Syntax_Embeddings.e_option d)
         (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_issue))
let nbe_e_ret_t :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      ('a FStar_Pervasives_Native.option * FStar_Tactics_V2_Basic.issues)
        FStar_TypeChecker_NBETerm.embedding
  =
  fun d ->
    solve
      (FStar_TypeChecker_NBETerm.e_tuple2
         (FStar_TypeChecker_NBETerm.e_option d)
         (FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_issue))
let (ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    FStar_Tactics_InterpFuns.mk_tot_step_1_psc Prims.int_zero "tracepoint"
      FStar_Tactics_Embedding.e_proofstate FStar_Syntax_Embeddings.e_bool
      FStar_Tactics_Embedding.e_proofstate_nbe
      FStar_TypeChecker_NBETerm.e_bool
      FStar_Tactics_Types.tracepoint_with_psc
      FStar_Tactics_Types.tracepoint_with_psc in
  let uu___1 =
    let uu___3 =
      FStar_Tactics_InterpFuns.mk_tot_step_2 Prims.int_zero
        "set_proofstate_range" FStar_Tactics_Embedding.e_proofstate
        FStar_Syntax_Embeddings.e_range FStar_Tactics_Embedding.e_proofstate
        FStar_Tactics_Embedding.e_proofstate_nbe
        FStar_TypeChecker_NBETerm.e_range
        FStar_Tactics_Embedding.e_proofstate_nbe
        FStar_Tactics_Types.set_proofstate_range
        FStar_Tactics_Types.set_proofstate_range in
    let uu___4 =
      let uu___5 =
        FStar_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero "incr_depth"
          FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Types.incr_depth FStar_Tactics_Types.incr_depth in
      let uu___6 =
        let uu___7 =
          FStar_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero "decr_depth"
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_Tactics_Types.decr_depth FStar_Tactics_Types.decr_depth in
        let uu___8 =
          let uu___9 =
            FStar_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero "goals_of"
              FStar_Tactics_Embedding.e_proofstate
              (FStar_Syntax_Embeddings.e_list FStar_Tactics_Embedding.e_goal)
              FStar_Tactics_Embedding.e_proofstate_nbe
              (FStar_TypeChecker_NBETerm.e_list
                 FStar_Tactics_Embedding.e_goal_nbe)
              FStar_Tactics_Types.goals_of FStar_Tactics_Types.goals_of in
          let uu___10 =
            let uu___11 =
              FStar_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                "smt_goals_of" FStar_Tactics_Embedding.e_proofstate
                (FStar_Syntax_Embeddings.e_list
                   FStar_Tactics_Embedding.e_goal)
                FStar_Tactics_Embedding.e_proofstate_nbe
                (FStar_TypeChecker_NBETerm.e_list
                   FStar_Tactics_Embedding.e_goal_nbe)
                FStar_Tactics_Types.smt_goals_of
                FStar_Tactics_Types.smt_goals_of in
            let uu___12 =
              let uu___13 =
                FStar_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                  "goal_env" FStar_Tactics_Embedding.e_goal
                  FStar_Reflection_V2_Embeddings.e_env
                  FStar_Tactics_Embedding.e_goal_nbe
                  FStar_Reflection_V2_NBEEmbeddings.e_env
                  FStar_Tactics_Types.goal_env FStar_Tactics_Types.goal_env in
              let uu___14 =
                let uu___15 =
                  FStar_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                    "goal_type" FStar_Tactics_Embedding.e_goal uu___2
                    FStar_Tactics_Embedding.e_goal_nbe
                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                    FStar_Tactics_Types.goal_type
                    FStar_Tactics_Types.goal_type in
                let uu___16 =
                  let uu___17 =
                    FStar_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                      "goal_witness" FStar_Tactics_Embedding.e_goal uu___2
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_V2_NBEEmbeddings.e_attribute
                      FStar_Tactics_Types.goal_witness
                      FStar_Tactics_Types.goal_witness in
                  let uu___18 =
                    let uu___19 =
                      FStar_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                        "is_guard" FStar_Tactics_Embedding.e_goal
                        FStar_Syntax_Embeddings.e_bool
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_TypeChecker_NBETerm.e_bool
                        FStar_Tactics_Types.is_guard
                        FStar_Tactics_Types.is_guard in
                    let uu___20 =
                      let uu___21 =
                        FStar_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                          "get_label" FStar_Tactics_Embedding.e_goal
                          FStar_Syntax_Embeddings.e_string
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_TypeChecker_NBETerm.e_string
                          FStar_Tactics_Types.get_label
                          FStar_Tactics_Types.get_label in
                      let uu___22 =
                        let uu___23 =
                          FStar_Tactics_InterpFuns.mk_tot_step_2
                            Prims.int_zero "set_label"
                            FStar_Syntax_Embeddings.e_string
                            FStar_Tactics_Embedding.e_goal
                            FStar_Tactics_Embedding.e_goal
                            FStar_TypeChecker_NBETerm.e_string
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_Tactics_Types.set_label
                            FStar_Tactics_Types.set_label in
                        let uu___24 =
                          let uu___25 =
                            let uu___26 =
                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                Prims.int_zero "compress" uu___2 uu___2
                                FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                FStar_Tactics_V2_Basic.compress
                                FStar_Tactics_V2_Basic.compress in
                            let uu___27 =
                              let uu___28 =
                                FStar_Tactics_InterpFuns.mk_tac_step_1
                                  Prims.int_zero "set_goals"
                                  (FStar_Syntax_Embeddings.e_list
                                     FStar_Tactics_Embedding.e_goal)
                                  FStar_Syntax_Embeddings.e_unit
                                  (FStar_TypeChecker_NBETerm.e_list
                                     FStar_Tactics_Embedding.e_goal_nbe)
                                  FStar_TypeChecker_NBETerm.e_unit
                                  FStar_Tactics_Monad.set_goals
                                  FStar_Tactics_Monad.set_goals in
                              let uu___29 =
                                let uu___30 =
                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                    Prims.int_zero "set_smt_goals"
                                    (FStar_Syntax_Embeddings.e_list
                                       FStar_Tactics_Embedding.e_goal)
                                    FStar_Syntax_Embeddings.e_unit
                                    (FStar_TypeChecker_NBETerm.e_list
                                       FStar_Tactics_Embedding.e_goal_nbe)
                                    FStar_TypeChecker_NBETerm.e_unit
                                    FStar_Tactics_Monad.set_smt_goals
                                    FStar_Tactics_Monad.set_smt_goals in
                                let uu___31 =
                                  let uu___32 =
                                    let uu___33 =
                                      FStar_Tactics_Interpreter.e_tactic_thunk
                                        FStar_Syntax_Embeddings.e_any in
                                    let uu___34 =
                                      FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                                        FStar_TypeChecker_NBETerm.e_any in
                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                      Prims.int_one "catch"
                                      FStar_Syntax_Embeddings.e_any uu___33
                                      (FStar_Syntax_Embeddings.e_either
                                         FStar_Tactics_Embedding.e_exn
                                         FStar_Syntax_Embeddings.e_any)
                                      FStar_TypeChecker_NBETerm.e_any uu___34
                                      (FStar_TypeChecker_NBETerm.e_either
                                         FStar_Tactics_Embedding.e_exn_nbe
                                         FStar_TypeChecker_NBETerm.e_any)
                                      (fun uu___35 ->
                                         FStar_Tactics_Monad.catch)
                                      (fun uu___35 ->
                                         FStar_Tactics_Monad.catch) in
                                  let uu___33 =
                                    let uu___34 =
                                      let uu___35 =
                                        FStar_Tactics_Interpreter.e_tactic_thunk
                                          FStar_Syntax_Embeddings.e_any in
                                      let uu___36 =
                                        FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                                          FStar_TypeChecker_NBETerm.e_any in
                                      FStar_Tactics_InterpFuns.mk_tac_step_2
                                        Prims.int_one "recover"
                                        FStar_Syntax_Embeddings.e_any uu___35
                                        (FStar_Syntax_Embeddings.e_either
                                           FStar_Tactics_Embedding.e_exn
                                           FStar_Syntax_Embeddings.e_any)
                                        FStar_TypeChecker_NBETerm.e_any
                                        uu___36
                                        (FStar_TypeChecker_NBETerm.e_either
                                           FStar_Tactics_Embedding.e_exn_nbe
                                           FStar_TypeChecker_NBETerm.e_any)
                                        (fun uu___37 ->
                                           FStar_Tactics_Monad.recover)
                                        (fun uu___37 ->
                                           FStar_Tactics_Monad.recover) in
                                    let uu___35 =
                                      let uu___36 =
                                        FStar_Tactics_InterpFuns.mk_tac_step_1
                                          Prims.int_zero "intro"
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Reflection_V2_Embeddings.e_binding
                                          FStar_TypeChecker_NBETerm.e_unit
                                          FStar_Reflection_V2_NBEEmbeddings.e_binding
                                          FStar_Tactics_V2_Basic.intro
                                          FStar_Tactics_V2_Basic.intro in
                                      let uu___37 =
                                        let uu___38 =
                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                            Prims.int_zero "intros"
                                            FStar_Syntax_Embeddings.e_int
                                            (FStar_Syntax_Embeddings.e_list
                                               FStar_Reflection_V2_Embeddings.e_binding)
                                            FStar_TypeChecker_NBETerm.e_int
                                            (FStar_TypeChecker_NBETerm.e_list
                                               FStar_Reflection_V2_NBEEmbeddings.e_binding)
                                            FStar_Tactics_V2_Basic.intros
                                            FStar_Tactics_V2_Basic.intros in
                                        let uu___39 =
                                          let uu___40 =
                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                              Prims.int_zero "intro_rec"
                                              FStar_Syntax_Embeddings.e_unit
                                              (FStar_Syntax_Embeddings.e_tuple2
                                                 FStar_Reflection_V2_Embeddings.e_binding
                                                 FStar_Reflection_V2_Embeddings.e_binding)
                                              FStar_TypeChecker_NBETerm.e_unit
                                              (FStar_TypeChecker_NBETerm.e_tuple2
                                                 FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                 FStar_Reflection_V2_NBEEmbeddings.e_binding)
                                              FStar_Tactics_V2_Basic.intro_rec
                                              FStar_Tactics_V2_Basic.intro_rec in
                                          let uu___41 =
                                            let uu___42 =
                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                Prims.int_zero "norm"
                                                (FStar_Syntax_Embeddings.e_list
                                                   FStar_Syntax_Embeddings.e_norm_step)
                                                FStar_Syntax_Embeddings.e_unit
                                                (FStar_TypeChecker_NBETerm.e_list
                                                   FStar_TypeChecker_NBETerm.e_norm_step)
                                                FStar_TypeChecker_NBETerm.e_unit
                                                FStar_Tactics_V2_Basic.norm
                                                FStar_Tactics_V2_Basic.norm in
                                            let uu___43 =
                                              let uu___44 =
                                                FStar_Tactics_InterpFuns.mk_tac_step_3
                                                  Prims.int_zero
                                                  "norm_term_env"
                                                  FStar_Reflection_V2_Embeddings.e_env
                                                  (FStar_Syntax_Embeddings.e_list
                                                     FStar_Syntax_Embeddings.e_norm_step)
                                                  uu___2 uu___2
                                                  FStar_Reflection_V2_NBEEmbeddings.e_env
                                                  (FStar_TypeChecker_NBETerm.e_list
                                                     FStar_TypeChecker_NBETerm.e_norm_step)
                                                  FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                  FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                  FStar_Tactics_V2_Basic.norm_term_env
                                                  FStar_Tactics_V2_Basic.norm_term_env in
                                              let uu___45 =
                                                let uu___46 =
                                                  FStar_Tactics_InterpFuns.mk_tac_step_2
                                                    Prims.int_zero
                                                    "norm_binding_type"
                                                    (FStar_Syntax_Embeddings.e_list
                                                       FStar_Syntax_Embeddings.e_norm_step)
                                                    FStar_Reflection_V2_Embeddings.e_binding
                                                    FStar_Syntax_Embeddings.e_unit
                                                    (FStar_TypeChecker_NBETerm.e_list
                                                       FStar_TypeChecker_NBETerm.e_norm_step)
                                                    FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                    FStar_TypeChecker_NBETerm.e_unit
                                                    FStar_Tactics_V2_Basic.norm_binding_type
                                                    FStar_Tactics_V2_Basic.norm_binding_type in
                                                let uu___47 =
                                                  let uu___48 =
                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                      Prims.int_zero
                                                      "rename_to"
                                                      FStar_Reflection_V2_Embeddings.e_binding
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_Reflection_V2_Embeddings.e_binding
                                                      FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                      FStar_TypeChecker_NBETerm.e_string
                                                      FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                      FStar_Tactics_V2_Basic.rename_to
                                                      FStar_Tactics_V2_Basic.rename_to in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      FStar_Tactics_InterpFuns.mk_tac_step_1
                                                        Prims.int_zero
                                                        "var_retype"
                                                        FStar_Reflection_V2_Embeddings.e_binding
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                        FStar_Tactics_V2_Basic.var_retype
                                                        FStar_Tactics_V2_Basic.var_retype in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        FStar_Tactics_InterpFuns.mk_tac_step_1
                                                          Prims.int_zero
                                                          "revert"
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                          FStar_Tactics_V2_Basic.revert
                                                          FStar_Tactics_V2_Basic.revert in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                                            Prims.int_zero
                                                            "clear_top"
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_Tactics_V2_Basic.clear_top
                                                            FStar_Tactics_V2_Basic.clear_top in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                                              Prims.int_zero
                                                              "clear"
                                                              FStar_Reflection_V2_Embeddings.e_binding
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                              FStar_Tactics_V2_Basic.clear
                                                              FStar_Tactics_V2_Basic.clear in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                Prims.int_zero
                                                                "rewrite"
                                                                FStar_Reflection_V2_Embeddings.e_binding
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Reflection_V2_NBEEmbeddings.e_binding
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                                FStar_Tactics_V2_Basic.rewrite
                                                                FStar_Tactics_V2_Basic.rewrite in
                                                            let uu___59 =
                                                              let uu___60 =
                                                                FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                  Prims.int_zero
                                                                  "grewrite"
                                                                  uu___2
                                                                  uu___2
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                  FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                  FStar_TypeChecker_NBETerm.e_unit
                                                                  FStar_Tactics_V2_Basic.grewrite
                                                                  FStar_Tactics_V2_Basic.grewrite in
                                                              let uu___61 =
                                                                let uu___62 =
                                                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "refine_intro"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.refine_intro
                                                                    FStar_Tactics_V2_Basic.refine_intro in
                                                                let uu___63 =
                                                                  let uu___64
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "t_exact"
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.t_exact
                                                                    FStar_Tactics_V2_Basic.t_exact in
                                                                  let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "t_apply"
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.t_apply
                                                                    FStar_Tactics_V2_Basic.t_apply in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "t_apply_lemma"
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.t_apply_lemma
                                                                    FStar_Tactics_V2_Basic.t_apply_lemma in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_options"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.set_options
                                                                    FStar_Tactics_V2_Basic.set_options in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "tcc"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    FStar_Reflection_V2_Embeddings.e_comp
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_comp
                                                                    FStar_Tactics_V2_Basic.tcc
                                                                    FStar_Tactics_V2_Basic.tcc in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "tc"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Tactics_V2_Basic.tc
                                                                    FStar_Tactics_V2_Basic.tc in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "unshelve"
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.unshelve
                                                                    FStar_Tactics_V2_Basic.unshelve in
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Tactics_V2_Basic.unquote
                                                                    (fun
                                                                    uu___79
                                                                    ->
                                                                    fun
                                                                    uu___80
                                                                    ->
                                                                    FStar_Compiler_Effect.failwith
                                                                    "NBE unquote") in
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "prune"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.prune
                                                                    FStar_Tactics_V2_Basic.prune in
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "addns"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.addns
                                                                    FStar_Tactics_V2_Basic.addns in
                                                                    let uu___83
                                                                    =
                                                                    let uu___84
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "print"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.print
                                                                    FStar_Tactics_V2_Basic.print in
                                                                    let uu___85
                                                                    =
                                                                    let uu___86
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "debugging"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V2_Basic.debugging
                                                                    FStar_Tactics_V2_Basic.debugging in
                                                                    let uu___87
                                                                    =
                                                                    let uu___88
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "ide"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V2_Basic.ide
                                                                    FStar_Tactics_V2_Basic.ide in
                                                                    let uu___89
                                                                    =
                                                                    let uu___90
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dump"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.dump
                                                                    FStar_Tactics_V2_Basic.dump in
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "dump_all"
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.dump_all
                                                                    FStar_Tactics_V2_Basic.dump_all in
                                                                    let uu___93
                                                                    =
                                                                    let uu___94
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "dump_uvars_of"
                                                                    FStar_Tactics_Embedding.e_goal
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_goal_nbe
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.dump_uvars_of
                                                                    FStar_Tactics_V2_Basic.dump_uvars_of in
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
                                                                    =
                                                                    let uu___97
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_1
                                                                    FStar_Reflection_V2_Embeddings.e_term
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag) in
                                                                    let uu___98
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu___99
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_nbe_1
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe) in
                                                                    let uu___100
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu___97
                                                                    uu___98
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu___99
                                                                    uu___100
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite in
                                                                    let uu___97
                                                                    =
                                                                    let uu___98
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_trefl"
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.t_trefl
                                                                    FStar_Tactics_V2_Basic.t_trefl in
                                                                    let uu___99
                                                                    =
                                                                    let uu___100
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dup"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.dup
                                                                    FStar_Tactics_V2_Basic.dup in
                                                                    let uu___101
                                                                    =
                                                                    let uu___102
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "tadmit_t"
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.tadmit_t
                                                                    FStar_Tactics_V2_Basic.tadmit_t in
                                                                    let uu___103
                                                                    =
                                                                    let uu___104
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "join"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.join
                                                                    FStar_Tactics_V2_Basic.join in
                                                                    let uu___105
                                                                    =
                                                                    let uu___106
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V2_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int))
                                                                    FStar_Tactics_V2_Basic.t_destruct
                                                                    FStar_Tactics_V2_Basic.t_destruct in
                                                                    let uu___107
                                                                    =
                                                                    let uu___108
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "top_env"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Tactics_V2_Basic.top_env
                                                                    FStar_Tactics_V2_Basic.top_env in
                                                                    let uu___109
                                                                    =
                                                                    let uu___110
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Tactics_V2_Basic.fresh
                                                                    FStar_Tactics_V2_Basic.fresh in
                                                                    let uu___111
                                                                    =
                                                                    let uu___112
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "curms"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Tactics_V2_Basic.curms
                                                                    FStar_Tactics_V2_Basic.curms in
                                                                    let uu___113
                                                                    =
                                                                    let uu___114
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    uu___2)
                                                                    uu___2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Tactics_V2_Basic.uvar_env
                                                                    FStar_Tactics_V2_Basic.uvar_env in
                                                                    let uu___115
                                                                    =
                                                                    let uu___116
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "ghost_uvar_env"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Tactics_V2_Basic.ghost_uvar_env
                                                                    FStar_Tactics_V2_Basic.ghost_uvar_env in
                                                                    let uu___117
                                                                    =
                                                                    let uu___118
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh_universe_uvar"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    uu___2
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Tactics_V2_Basic.fresh_universe_uvar
                                                                    FStar_Tactics_V2_Basic.fresh_universe_uvar in
                                                                    let uu___119
                                                                    =
                                                                    let uu___120
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "unify_env"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V2_Basic.unify_env
                                                                    FStar_Tactics_V2_Basic.unify_env in
                                                                    let uu___121
                                                                    =
                                                                    let uu___122
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "unify_guard_env"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V2_Basic.unify_guard_env
                                                                    FStar_Tactics_V2_Basic.unify_guard_env in
                                                                    let uu___123
                                                                    =
                                                                    let uu___124
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "match_env"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V2_Basic.match_env
                                                                    FStar_Tactics_V2_Basic.match_env in
                                                                    let uu___125
                                                                    =
                                                                    let uu___126
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Tactics_V2_Basic.launch_process
                                                                    FStar_Tactics_V2_Basic.launch_process in
                                                                    let uu___127
                                                                    =
                                                                    let uu___128
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "change"
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.change
                                                                    FStar_Tactics_V2_Basic.change in
                                                                    let uu___129
                                                                    =
                                                                    let uu___130
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "get_guard_policy"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_Tactics_V2_Basic.get_guard_policy
                                                                    FStar_Tactics_V2_Basic.get_guard_policy in
                                                                    let uu___131
                                                                    =
                                                                    let uu___132
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.set_guard_policy
                                                                    FStar_Tactics_V2_Basic.set_guard_policy in
                                                                    let uu___133
                                                                    =
                                                                    let uu___134
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "lax_on"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V2_Basic.lax_on
                                                                    FStar_Tactics_V2_Basic.lax_on in
                                                                    let uu___135
                                                                    =
                                                                    let uu___136
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Tactics_V2_Basic.lget
                                                                    (fun
                                                                    uu___137
                                                                    ->
                                                                    fun
                                                                    uu___138
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE") in
                                                                    let uu___137
                                                                    =
                                                                    let uu___138
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "lset"
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.lset
                                                                    (fun
                                                                    uu___139
                                                                    ->
                                                                    fun
                                                                    uu___140
                                                                    ->
                                                                    fun
                                                                    uu___141
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE") in
                                                                    let uu___139
                                                                    =
                                                                    let uu___140
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_one
                                                                    "set_urgency"
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.set_urgency
                                                                    FStar_Tactics_V2_Basic.set_urgency in
                                                                    let uu___141
                                                                    =
                                                                    let uu___142
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_one
                                                                    "set_dump_on_failure"
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.set_dump_on_failure
                                                                    FStar_Tactics_V2_Basic.set_dump_on_failure in
                                                                    let uu___143
                                                                    =
                                                                    let uu___144
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_one
                                                                    "t_commute_applied_match"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.t_commute_applied_match
                                                                    FStar_Tactics_V2_Basic.t_commute_applied_match in
                                                                    let uu___145
                                                                    =
                                                                    let uu___146
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "gather_or_solve_explicit_guards_for_resolved_goals"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.gather_explicit_guards_for_resolved_goals
                                                                    FStar_Tactics_V2_Basic.gather_explicit_guards_for_resolved_goals in
                                                                    let uu___147
                                                                    =
                                                                    let uu___148
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "string_to_term"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu___2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Tactics_V2_Basic.string_to_term
                                                                    FStar_Tactics_V2_Basic.string_to_term in
                                                                    let uu___149
                                                                    =
                                                                    let uu___150
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "push_bv_dsenv"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_Embeddings.e_binding)
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_binding)
                                                                    FStar_Tactics_V2_Basic.push_bv_dsenv
                                                                    FStar_Tactics_V2_Basic.push_bv_dsenv in
                                                                    let uu___151
                                                                    =
                                                                    let uu___152
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "term_to_string"
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Tactics_V2_Basic.term_to_string
                                                                    FStar_Tactics_V2_Basic.term_to_string in
                                                                    let uu___153
                                                                    =
                                                                    let uu___154
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "comp_to_string"
                                                                    FStar_Reflection_V2_Embeddings.e_comp
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_comp
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Tactics_V2_Basic.comp_to_string
                                                                    FStar_Tactics_V2_Basic.comp_to_string in
                                                                    let uu___155
                                                                    =
                                                                    let uu___156
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "term_to_doc"
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Tactics_V2_Basic.term_to_doc
                                                                    FStar_Tactics_V2_Basic.term_to_doc in
                                                                    let uu___157
                                                                    =
                                                                    let uu___158
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "comp_to_doc"
                                                                    FStar_Reflection_V2_Embeddings.e_comp
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_comp
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Tactics_V2_Basic.comp_to_doc
                                                                    FStar_Tactics_V2_Basic.comp_to_doc in
                                                                    let uu___159
                                                                    =
                                                                    let uu___160
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "range_to_string"
                                                                    FStar_Syntax_Embeddings.e_range
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_TypeChecker_NBETerm.e_range
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Tactics_V2_Basic.range_to_string
                                                                    FStar_Tactics_V2_Basic.range_to_string in
                                                                    let uu___161
                                                                    =
                                                                    let uu___162
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "term_eq_old"
                                                                    uu___2
                                                                    uu___2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V2_Basic.term_eq_old
                                                                    FStar_Tactics_V2_Basic.term_eq_old in
                                                                    let uu___163
                                                                    =
                                                                    let uu___164
                                                                    =
                                                                    let uu___165
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_any in
                                                                    let uu___166
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "with_compat_pre_core"
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    uu___165
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    uu___166
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    (fun
                                                                    uu___167
                                                                    ->
                                                                    FStar_Tactics_V2_Basic.with_compat_pre_core)
                                                                    (fun
                                                                    uu___167
                                                                    ->
                                                                    FStar_Tactics_V2_Basic.with_compat_pre_core) in
                                                                    let uu___165
                                                                    =
                                                                    let uu___166
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "get_vconfig"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_vconfig
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_vconfig
                                                                    FStar_Tactics_V2_Basic.get_vconfig
                                                                    FStar_Tactics_V2_Basic.get_vconfig in
                                                                    let uu___167
                                                                    =
                                                                    let uu___168
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_vconfig"
                                                                    FStar_Syntax_Embeddings.e_vconfig
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_vconfig
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.set_vconfig
                                                                    FStar_Tactics_V2_Basic.set_vconfig in
                                                                    let uu___169
                                                                    =
                                                                    let uu___170
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_smt_sync"
                                                                    FStar_Syntax_Embeddings.e_vconfig
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_vconfig
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.t_smt_sync
                                                                    FStar_Tactics_V2_Basic.t_smt_sync in
                                                                    let uu___171
                                                                    =
                                                                    let uu___172
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "free_uvars"
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_int)
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_int)
                                                                    FStar_Tactics_V2_Basic.free_uvars
                                                                    FStar_Tactics_V2_Basic.free_uvars in
                                                                    let uu___173
                                                                    =
                                                                    let uu___174
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "all_ext_options"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string))
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string))
                                                                    FStar_Tactics_V2_Basic.all_ext_options
                                                                    FStar_Tactics_V2_Basic.all_ext_options in
                                                                    let uu___175
                                                                    =
                                                                    let uu___176
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "ext_getv"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Tactics_V2_Basic.ext_getv
                                                                    FStar_Tactics_V2_Basic.ext_getv in
                                                                    let uu___177
                                                                    =
                                                                    let uu___178
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "ext_getns"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string))
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string))
                                                                    FStar_Tactics_V2_Basic.ext_getns
                                                                    FStar_Tactics_V2_Basic.ext_getns in
                                                                    let uu___179
                                                                    =
                                                                    let uu___180
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "alloc"
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (FStar_Tactics_Embedding.e_tref
                                                                    ())
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    (FStar_Tactics_Embedding.e_tref_nbe
                                                                    ())
                                                                    (fun
                                                                    uu___181
                                                                    ->
                                                                    FStar_Tactics_V2_Basic.alloc)
                                                                    (fun
                                                                    uu___181
                                                                    ->
                                                                    FStar_Tactics_V2_Basic.alloc) in
                                                                    let uu___181
                                                                    =
                                                                    let uu___182
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "read"
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (FStar_Tactics_Embedding.e_tref
                                                                    ())
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    (FStar_Tactics_Embedding.e_tref_nbe
                                                                    ())
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    (fun
                                                                    uu___183
                                                                    ->
                                                                    FStar_Tactics_V2_Basic.read)
                                                                    (fun
                                                                    uu___183
                                                                    ->
                                                                    FStar_Tactics_V2_Basic.read) in
                                                                    let uu___183
                                                                    =
                                                                    let uu___184
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "write"
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (FStar_Tactics_Embedding.e_tref
                                                                    ())
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    (FStar_Tactics_Embedding.e_tref_nbe
                                                                    ())
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    (fun
                                                                    uu___185
                                                                    ->
                                                                    FStar_Tactics_V2_Basic.write)
                                                                    (fun
                                                                    uu___185
                                                                    ->
                                                                    FStar_Tactics_V2_Basic.write) in
                                                                    let uu___185
                                                                    =
                                                                    let uu___186
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "is_non_informative"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_TypeChecker_NBETerm.e_unit)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.refl_is_non_informative
                                                                    FStar_Tactics_V2_Basic.refl_is_non_informative in
                                                                    let uu___187
                                                                    =
                                                                    let uu___188
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "check_subtyping"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_TypeChecker_NBETerm.e_unit)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.refl_check_subtyping
                                                                    FStar_Tactics_V2_Basic.refl_check_subtyping in
                                                                    let uu___189
                                                                    =
                                                                    let uu___190
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_5
                                                                    Prims.int_zero
                                                                    "t_check_equiv"
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_TypeChecker_NBETerm.e_unit)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.t_refl_check_equiv
                                                                    FStar_Tactics_V2_Basic.t_refl_check_equiv in
                                                                    let uu___191
                                                                    =
                                                                    let uu___192
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "core_compute_term_type"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost
                                                                    uu___2))
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost_nbe
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute))
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.refl_core_compute_term_type
                                                                    FStar_Tactics_V2_Basic.refl_core_compute_term_type in
                                                                    let uu___193
                                                                    =
                                                                    let uu___194
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "core_check_term"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost_nbe
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_TypeChecker_NBETerm.e_unit)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.refl_core_check_term
                                                                    FStar_Tactics_V2_Basic.refl_core_check_term in
                                                                    let uu___195
                                                                    =
                                                                    let uu___196
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "core_check_term_at_type"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost_nbe)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.refl_core_check_term_at_type
                                                                    FStar_Tactics_V2_Basic.refl_core_check_term_at_type in
                                                                    let uu___197
                                                                    =
                                                                    let uu___198
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "tc_term"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost
                                                                    uu___2)))
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Tactics_Embedding.e_tot_or_ghost_nbe
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute)))
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.refl_tc_term
                                                                    FStar_Tactics_V2_Basic.refl_tc_term in
                                                                    let uu___199
                                                                    =
                                                                    let uu___200
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "universe_of"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_V2_Embeddings.e_universe)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_universe)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.refl_universe_of
                                                                    FStar_Tactics_V2_Basic.refl_universe_of in
                                                                    let uu___201
                                                                    =
                                                                    let uu___202
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "check_prop_validity"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    FStar_Syntax_Embeddings.e_unit)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_TypeChecker_NBETerm.e_unit)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.refl_check_prop_validity
                                                                    FStar_Tactics_V2_Basic.refl_check_prop_validity in
                                                                    let uu___203
                                                                    =
                                                                    let uu___204
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "check_match_complete"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Reflection_V2_Embeddings.e_pattern)
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Reflection_V2_Embeddings.e_pattern)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Reflection_V2_Embeddings.e_binding))))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_pattern)
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_pattern)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_binding))))
                                                                    FStar_Tactics_V2_Basic.refl_check_match_complete
                                                                    FStar_Tactics_V2_Basic.refl_check_match_complete in
                                                                    let uu___205
                                                                    =
                                                                    let uu___206
                                                                    =
                                                                    let uu___207
                                                                    =
                                                                    e_ret_t
                                                                    (FStar_Syntax_Embeddings.e_tuple3
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V2_Embeddings.e_namedv
                                                                    (solve
                                                                    uu___2)))
                                                                    (solve
                                                                    uu___2)
                                                                    (solve
                                                                    uu___2)) in
                                                                    let uu___208
                                                                    =
                                                                    nbe_e_ret_t
                                                                    (FStar_TypeChecker_NBETerm.e_tuple3
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_namedv
                                                                    (solve
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute)))
                                                                    (solve
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    (solve
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute)) in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "instantiate_implicits"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    uu___2)
                                                                    uu___207
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    uu___208
                                                                    FStar_Tactics_V2_Basic.refl_instantiate_implicits
                                                                    FStar_Tactics_V2_Basic.refl_instantiate_implicits in
                                                                    let uu___207
                                                                    =
                                                                    let uu___208
                                                                    =
                                                                    let uu___209
                                                                    =
                                                                    e_ret_t
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V2_Embeddings.e_namedv
                                                                    FStar_Reflection_V2_Embeddings.e_term)) in
                                                                    let uu___210
                                                                    =
                                                                    nbe_e_ret_t
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_namedv
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term)) in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "try_unify"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V2_Embeddings.e_namedv
                                                                    FStar_Reflection_V2_Embeddings.e_term))
                                                                    uu___2
                                                                    uu___2
                                                                    uu___209
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_namedv
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_term))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    uu___210
                                                                    FStar_Tactics_V2_Basic.refl_try_unify
                                                                    FStar_Tactics_V2_Basic.refl_try_unify in
                                                                    let uu___209
                                                                    =
                                                                    let uu___210
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "maybe_relate_after_unfolding"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    FStar_Tactics_Embedding.e_unfold_side)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Tactics_Embedding.e_unfold_side_nbe)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.refl_maybe_relate_after_unfolding
                                                                    FStar_Tactics_V2_Basic.refl_maybe_relate_after_unfolding in
                                                                    let uu___211
                                                                    =
                                                                    let uu___212
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "maybe_unfold_head"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    uu___2)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.refl_maybe_unfold_head
                                                                    FStar_Tactics_V2_Basic.refl_maybe_unfold_head in
                                                                    let uu___213
                                                                    =
                                                                    let uu___214
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "norm_well_typed_term"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_norm_step)
                                                                    uu___2
                                                                    uu___2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_norm_step)
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Tactics_V2_Basic.refl_norm_well_typed_term
                                                                    FStar_Tactics_V2_Basic.refl_norm_well_typed_term in
                                                                    let uu___215
                                                                    =
                                                                    let uu___216
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "push_open_namespace"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Tactics_V2_Basic.push_open_namespace
                                                                    FStar_Tactics_V2_Basic.push_open_namespace in
                                                                    let uu___217
                                                                    =
                                                                    let uu___218
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "push_module_abbrev"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Tactics_V2_Basic.push_module_abbrev
                                                                    FStar_Tactics_V2_Basic.push_module_abbrev in
                                                                    let uu___219
                                                                    =
                                                                    let uu___220
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "resolve_name"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Syntax_Embeddings.e_string_list
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    (FStar_Syntax_Embeddings.e_either
                                                                    FStar_Reflection_V2_Embeddings.e_bv
                                                                    (solve
                                                                    FStar_Reflection_V2_Embeddings.e_fv)))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_string_list
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    (FStar_TypeChecker_NBETerm.e_either
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_bv
                                                                    (solve
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_fv)))
                                                                    FStar_Tactics_V2_Basic.resolve_name
                                                                    FStar_Tactics_V2_Basic.resolve_name in
                                                                    let uu___221
                                                                    =
                                                                    let uu___222
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "log_issues"
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue)
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue)
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V2_Basic.log_issues
                                                                    FStar_Tactics_V2_Basic.log_issues in
                                                                    let uu___223
                                                                    =
                                                                    let uu___224
                                                                    =
                                                                    let uu___225
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu___226
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "call_subtac"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___225
                                                                    FStar_Reflection_V2_Embeddings.e_universe
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    uu___2)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    uu___226
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_universe
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.call_subtac
                                                                    FStar_Tactics_V2_Basic.call_subtac in
                                                                    let uu___225
                                                                    =
                                                                    let uu___226
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "call_subtac_tm"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    uu___2
                                                                    FStar_Reflection_V2_Embeddings.e_universe
                                                                    uu___2
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    uu___2)
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_issue))
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_universe
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_issue))
                                                                    FStar_Tactics_V2_Basic.call_subtac_tm
                                                                    FStar_Tactics_V2_Basic.call_subtac_tm in
                                                                    [uu___226] in
                                                                    uu___224
                                                                    ::
                                                                    uu___225 in
                                                                    uu___222
                                                                    ::
                                                                    uu___223 in
                                                                    uu___220
                                                                    ::
                                                                    uu___221 in
                                                                    uu___218
                                                                    ::
                                                                    uu___219 in
                                                                    uu___216
                                                                    ::
                                                                    uu___217 in
                                                                    uu___214
                                                                    ::
                                                                    uu___215 in
                                                                    uu___212
                                                                    ::
                                                                    uu___213 in
                                                                    uu___210
                                                                    ::
                                                                    uu___211 in
                                                                    uu___208
                                                                    ::
                                                                    uu___209 in
                                                                    uu___206
                                                                    ::
                                                                    uu___207 in
                                                                    uu___204
                                                                    ::
                                                                    uu___205 in
                                                                    uu___202
                                                                    ::
                                                                    uu___203 in
                                                                    uu___200
                                                                    ::
                                                                    uu___201 in
                                                                    uu___198
                                                                    ::
                                                                    uu___199 in
                                                                    uu___196
                                                                    ::
                                                                    uu___197 in
                                                                    uu___194
                                                                    ::
                                                                    uu___195 in
                                                                    uu___192
                                                                    ::
                                                                    uu___193 in
                                                                    uu___190
                                                                    ::
                                                                    uu___191 in
                                                                    uu___188
                                                                    ::
                                                                    uu___189 in
                                                                    uu___186
                                                                    ::
                                                                    uu___187 in
                                                                    uu___184
                                                                    ::
                                                                    uu___185 in
                                                                    uu___182
                                                                    ::
                                                                    uu___183 in
                                                                    uu___180
                                                                    ::
                                                                    uu___181 in
                                                                    uu___178
                                                                    ::
                                                                    uu___179 in
                                                                    uu___176
                                                                    ::
                                                                    uu___177 in
                                                                    uu___174
                                                                    ::
                                                                    uu___175 in
                                                                    uu___172
                                                                    ::
                                                                    uu___173 in
                                                                    uu___170
                                                                    ::
                                                                    uu___171 in
                                                                    uu___168
                                                                    ::
                                                                    uu___169 in
                                                                    uu___166
                                                                    ::
                                                                    uu___167 in
                                                                    uu___164
                                                                    ::
                                                                    uu___165 in
                                                                    uu___162
                                                                    ::
                                                                    uu___163 in
                                                                    uu___160
                                                                    ::
                                                                    uu___161 in
                                                                    uu___158
                                                                    ::
                                                                    uu___159 in
                                                                    uu___156
                                                                    ::
                                                                    uu___157 in
                                                                    uu___154
                                                                    ::
                                                                    uu___155 in
                                                                    uu___152
                                                                    ::
                                                                    uu___153 in
                                                                    uu___150
                                                                    ::
                                                                    uu___151 in
                                                                    uu___148
                                                                    ::
                                                                    uu___149 in
                                                                    uu___146
                                                                    ::
                                                                    uu___147 in
                                                                    uu___144
                                                                    ::
                                                                    uu___145 in
                                                                    uu___142
                                                                    ::
                                                                    uu___143 in
                                                                    uu___140
                                                                    ::
                                                                    uu___141 in
                                                                    uu___138
                                                                    ::
                                                                    uu___139 in
                                                                    uu___136
                                                                    ::
                                                                    uu___137 in
                                                                    uu___134
                                                                    ::
                                                                    uu___135 in
                                                                    uu___132
                                                                    ::
                                                                    uu___133 in
                                                                    uu___130
                                                                    ::
                                                                    uu___131 in
                                                                    uu___128
                                                                    ::
                                                                    uu___129 in
                                                                    uu___126
                                                                    ::
                                                                    uu___127 in
                                                                    uu___124
                                                                    ::
                                                                    uu___125 in
                                                                    uu___122
                                                                    ::
                                                                    uu___123 in
                                                                    uu___120
                                                                    ::
                                                                    uu___121 in
                                                                    uu___118
                                                                    ::
                                                                    uu___119 in
                                                                    uu___116
                                                                    ::
                                                                    uu___117 in
                                                                    uu___114
                                                                    ::
                                                                    uu___115 in
                                                                    uu___112
                                                                    ::
                                                                    uu___113 in
                                                                    uu___110
                                                                    ::
                                                                    uu___111 in
                                                                    uu___108
                                                                    ::
                                                                    uu___109 in
                                                                    uu___106
                                                                    ::
                                                                    uu___107 in
                                                                    uu___104
                                                                    ::
                                                                    uu___105 in
                                                                    uu___102
                                                                    ::
                                                                    uu___103 in
                                                                    uu___100
                                                                    ::
                                                                    uu___101 in
                                                                    uu___98
                                                                    ::
                                                                    uu___99 in
                                                                    uu___96
                                                                    ::
                                                                    uu___97 in
                                                                    uu___94
                                                                    ::
                                                                    uu___95 in
                                                                    uu___92
                                                                    ::
                                                                    uu___93 in
                                                                    uu___90
                                                                    ::
                                                                    uu___91 in
                                                                    uu___88
                                                                    ::
                                                                    uu___89 in
                                                                    uu___86
                                                                    ::
                                                                    uu___87 in
                                                                    uu___84
                                                                    ::
                                                                    uu___85 in
                                                                    uu___82
                                                                    ::
                                                                    uu___83 in
                                                                    uu___80
                                                                    ::
                                                                    uu___81 in
                                                                    uu___78
                                                                    ::
                                                                    uu___79 in
                                                                    uu___76
                                                                    ::
                                                                    uu___77 in
                                                                    uu___74
                                                                    ::
                                                                    uu___75 in
                                                                    uu___72
                                                                    ::
                                                                    uu___73 in
                                                                    uu___70
                                                                    ::
                                                                    uu___71 in
                                                                    uu___68
                                                                    ::
                                                                    uu___69 in
                                                                    uu___66
                                                                    ::
                                                                    uu___67 in
                                                                  uu___64 ::
                                                                    uu___65 in
                                                                uu___62 ::
                                                                  uu___63 in
                                                              uu___60 ::
                                                                uu___61 in
                                                            uu___58 ::
                                                              uu___59 in
                                                          uu___56 :: uu___57 in
                                                        uu___54 :: uu___55 in
                                                      uu___52 :: uu___53 in
                                                    uu___50 :: uu___51 in
                                                  uu___48 :: uu___49 in
                                                uu___46 :: uu___47 in
                                              uu___44 :: uu___45 in
                                            uu___42 :: uu___43 in
                                          uu___40 :: uu___41 in
                                        uu___38 :: uu___39 in
                                      uu___36 :: uu___37 in
                                    uu___34 :: uu___35 in
                                  uu___32 :: uu___33 in
                                uu___30 :: uu___31 in
                              uu___28 :: uu___29 in
                            uu___26 :: uu___27 in
                          unseal_step :: uu___25 in
                        uu___23 :: uu___24 in
                      uu___21 :: uu___22 in
                    uu___19 :: uu___20 in
                  uu___17 :: uu___18 in
                uu___15 :: uu___16 in
              uu___13 :: uu___14 in
            uu___11 :: uu___12 in
          uu___9 :: uu___10 in
        uu___7 :: uu___8 in
      uu___5 :: uu___6 in
    uu___3 :: uu___4 in
  uu___ :: uu___1