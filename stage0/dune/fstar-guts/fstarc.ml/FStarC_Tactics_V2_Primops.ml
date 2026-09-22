open Prims
let solve (ev : 'a) : 'a= ev
let uu___0 :
  FStarC_Syntax_Syntax.term FStarC_Syntax_Embeddings_Base.embedding=
  FStarC_Reflection_V2_Embeddings.e_term
let e_ret_t (d : 'a FStarC_Syntax_Embeddings_Base.embedding) :
  ('a FStar_Pervasives_Native.option * FStarC_Tactics_V2_Basic.issues)
    FStarC_Syntax_Embeddings_Base.embedding=
  FStarC_Syntax_Embeddings.e_tuple2 (FStarC_Syntax_Embeddings.e_option d)
    (FStarC_Syntax_Embeddings.e_list FStarC_Syntax_Embeddings.e_issue)
let nbe_e_ret_t (d : 'a FStarC_TypeChecker_NBETerm.embedding) :
  ('a FStar_Pervasives_Native.option * FStarC_Tactics_V2_Basic.issues)
    FStarC_TypeChecker_NBETerm.embedding=
  FStarC_TypeChecker_NBETerm.e_tuple2 (FStarC_TypeChecker_NBETerm.e_option d)
    (FStarC_TypeChecker_NBETerm.e_list FStarC_TypeChecker_NBETerm.e_issue)
let ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  let uu___ =
    FStarC_Tactics_InterpFuns.mk_tot_step_1_psc Prims.int_zero "tracepoint"
      FStarC_Tactics_Embedding.e_proofstate FStarC_Syntax_Embeddings.e_bool
      FStarC_Tactics_Embedding.e_proofstate_nbe
      FStarC_TypeChecker_NBETerm.e_bool
      FStarC_Tactics_Types.tracepoint_with_psc
      FStarC_Tactics_Types.tracepoint_with_psc in
  let uu___1 =
    let uu___2 =
      FStarC_Tactics_InterpFuns.mk_tot_step_2 Prims.int_zero
        "set_proofstate_range" FStarC_Tactics_Embedding.e_proofstate
        FStarC_Syntax_Embeddings.e_range
        FStarC_Tactics_Embedding.e_proofstate
        FStarC_Tactics_Embedding.e_proofstate_nbe
        FStarC_TypeChecker_NBETerm.e_range
        FStarC_Tactics_Embedding.e_proofstate_nbe
        FStarC_Tactics_Types.set_proofstate_range
        FStarC_Tactics_Types.set_proofstate_range in
    let uu___3 =
      let uu___4 =
        FStarC_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero "incr_depth"
          FStarC_Tactics_Embedding.e_proofstate
          FStarC_Tactics_Embedding.e_proofstate
          FStarC_Tactics_Embedding.e_proofstate_nbe
          FStarC_Tactics_Embedding.e_proofstate_nbe
          FStarC_Tactics_Types.incr_depth FStarC_Tactics_Types.incr_depth in
      let uu___5 =
        let uu___6 =
          FStarC_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero "decr_depth"
            FStarC_Tactics_Embedding.e_proofstate
            FStarC_Tactics_Embedding.e_proofstate
            FStarC_Tactics_Embedding.e_proofstate_nbe
            FStarC_Tactics_Embedding.e_proofstate_nbe
            FStarC_Tactics_Types.decr_depth FStarC_Tactics_Types.decr_depth in
        let uu___7 =
          let uu___8 =
            FStarC_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero "goals_of"
              FStarC_Tactics_Embedding.e_proofstate
              (FStarC_Syntax_Embeddings.e_list
                 FStarC_Tactics_Embedding.e_goal)
              FStarC_Tactics_Embedding.e_proofstate_nbe
              (FStarC_TypeChecker_NBETerm.e_list
                 FStarC_Tactics_Embedding.e_goal_nbe)
              FStarC_Tactics_Types.goals_of FStarC_Tactics_Types.goals_of in
          let uu___9 =
            let uu___10 =
              FStarC_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                "smt_goals_of" FStarC_Tactics_Embedding.e_proofstate
                (FStarC_Syntax_Embeddings.e_list
                   FStarC_Tactics_Embedding.e_goal)
                FStarC_Tactics_Embedding.e_proofstate_nbe
                (FStarC_TypeChecker_NBETerm.e_list
                   FStarC_Tactics_Embedding.e_goal_nbe)
                FStarC_Tactics_Types.smt_goals_of
                FStarC_Tactics_Types.smt_goals_of in
            let uu___11 =
              let uu___12 =
                FStarC_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                  "goal_env" FStarC_Tactics_Embedding.e_goal
                  FStarC_Reflection_V2_Embeddings.e_env
                  FStarC_Tactics_Embedding.e_goal_nbe
                  FStarC_Reflection_V2_NBEEmbeddings.e_env
                  FStarC_Tactics_Types.goal_env FStarC_Tactics_Types.goal_env in
              let uu___13 =
                let uu___14 =
                  FStarC_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                    "goal_type" FStarC_Tactics_Embedding.e_goal uu___0
                    FStarC_Tactics_Embedding.e_goal_nbe
                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                    FStarC_Tactics_Types.goal_type
                    FStarC_Tactics_Types.goal_type in
                let uu___15 =
                  let uu___16 =
                    FStarC_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                      "goal_witness" FStarC_Tactics_Embedding.e_goal uu___0
                      FStarC_Tactics_Embedding.e_goal_nbe
                      FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                      FStarC_Tactics_Types.goal_witness
                      FStarC_Tactics_Types.goal_witness in
                  let uu___17 =
                    let uu___18 =
                      FStarC_Tactics_InterpFuns.mk_tot_step_1 Prims.int_zero
                        "is_guard" FStarC_Tactics_Embedding.e_goal
                        FStarC_Syntax_Embeddings.e_bool
                        FStarC_Tactics_Embedding.e_goal_nbe
                        FStarC_TypeChecker_NBETerm.e_bool
                        FStarC_Tactics_Types.is_guard
                        FStarC_Tactics_Types.is_guard in
                    let uu___19 =
                      let uu___20 =
                        FStarC_Tactics_InterpFuns.mk_tot_step_1
                          Prims.int_zero "get_label"
                          FStarC_Tactics_Embedding.e_goal
                          FStarC_Syntax_Embeddings.e_string
                          FStarC_Tactics_Embedding.e_goal_nbe
                          FStarC_TypeChecker_NBETerm.e_string
                          FStarC_Tactics_Types.get_label
                          FStarC_Tactics_Types.get_label in
                      let uu___21 =
                        let uu___22 =
                          FStarC_Tactics_InterpFuns.mk_tot_step_2
                            Prims.int_zero "set_label"
                            FStarC_Syntax_Embeddings.e_string
                            FStarC_Tactics_Embedding.e_goal
                            FStarC_Tactics_Embedding.e_goal
                            FStarC_TypeChecker_NBETerm.e_string
                            FStarC_Tactics_Embedding.e_goal_nbe
                            FStarC_Tactics_Embedding.e_goal_nbe
                            FStarC_Tactics_Types.set_label
                            FStarC_Tactics_Types.set_label in
                        let uu___23 =
                          let uu___24 =
                            FStarC_Tactics_InterpFuns.mk_tac_step_1
                              Prims.int_zero "get"
                              FStarC_Syntax_Embeddings.e_unit
                              FStarC_Tactics_Embedding.e_proofstate
                              FStarC_TypeChecker_NBETerm.e_unit
                              FStarC_Tactics_Embedding.e_proofstate_nbe
                              (fun uu___25 -> FStarC_Tactics_Monad.get)
                              (fun uu___25 -> FStarC_Tactics_Monad.get) in
                          let uu___25 =
                            let uu___26 =
                              FStarC_Tactics_InterpFuns.mk_tac_step_1
                                Prims.int_zero "fixup_range"
                                FStarC_Syntax_Embeddings.e_range
                                FStarC_Syntax_Embeddings.e_range
                                FStarC_TypeChecker_NBETerm.e_range
                                FStarC_TypeChecker_NBETerm.e_range
                                FStarC_Tactics_V2_Basic.fixup_range
                                FStarC_Tactics_V2_Basic.fixup_range in
                            let uu___27 =
                              let uu___28 =
                                FStarC_Tactics_InterpFuns.mk_tac_step_1
                                  Prims.int_zero "compress" uu___0 uu___0
                                  FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                  FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                  FStarC_Tactics_V2_Basic.compress
                                  FStarC_Tactics_V2_Basic.compress in
                              let uu___29 =
                                let uu___30 =
                                  FStarC_Tactics_InterpFuns.mk_tac_step_1
                                    Prims.int_zero "set_goals"
                                    (FStarC_Syntax_Embeddings.e_list
                                       FStarC_Tactics_Embedding.e_goal)
                                    FStarC_Syntax_Embeddings.e_unit
                                    (FStarC_TypeChecker_NBETerm.e_list
                                       FStarC_Tactics_Embedding.e_goal_nbe)
                                    FStarC_TypeChecker_NBETerm.e_unit
                                    FStarC_Tactics_Monad.set_goals
                                    FStarC_Tactics_Monad.set_goals in
                                let uu___31 =
                                  let uu___32 =
                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                      Prims.int_zero "set_smt_goals"
                                      (FStarC_Syntax_Embeddings.e_list
                                         FStarC_Tactics_Embedding.e_goal)
                                      FStarC_Syntax_Embeddings.e_unit
                                      (FStarC_TypeChecker_NBETerm.e_list
                                         FStarC_Tactics_Embedding.e_goal_nbe)
                                      FStarC_TypeChecker_NBETerm.e_unit
                                      FStarC_Tactics_Monad.set_smt_goals
                                      FStarC_Tactics_Monad.set_smt_goals in
                                  let uu___33 =
                                    let uu___34 =
                                      let uu___35 =
                                        FStarC_Tactics_Interpreter.e_tactic_thunk
                                          FStarC_Syntax_Embeddings.e_any in
                                      let uu___36 =
                                        FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                          FStarC_TypeChecker_NBETerm.e_any in
                                      FStarC_Tactics_InterpFuns.mk_tac_step_2
                                        Prims.int_one "catch"
                                        FStarC_Syntax_Embeddings.e_any
                                        uu___35
                                        (FStarC_Syntax_Embeddings.e_either
                                           FStarC_Tactics_Embedding.e_exn
                                           FStarC_Syntax_Embeddings.e_any)
                                        FStarC_TypeChecker_NBETerm.e_any
                                        uu___36
                                        (FStarC_TypeChecker_NBETerm.e_either
                                           FStarC_Tactics_Embedding.e_exn_nbe
                                           FStarC_TypeChecker_NBETerm.e_any)
                                        (fun uu___37 ->
                                           FStarC_Tactics_Monad.catch)
                                        (fun uu___37 ->
                                           FStarC_Tactics_Monad.catch) in
                                    let uu___35 =
                                      let uu___36 =
                                        FStarC_Tactics_InterpFuns.mk_tac_step_1
                                          Prims.int_zero "raise_core"
                                          FStarC_Tactics_Embedding.e_exn
                                          FStarC_Syntax_Embeddings.e_unit
                                          FStarC_Tactics_Embedding.e_exn_nbe
                                          FStarC_TypeChecker_NBETerm.e_unit
                                          FStarC_Tactics_Monad.traise
                                          FStarC_Tactics_Monad.traise in
                                      let uu___37 =
                                        let uu___38 =
                                          FStarC_Tactics_InterpFuns.mk_tac_step_1
                                            Prims.int_zero "intro"
                                            FStarC_Syntax_Embeddings.e_unit
                                            FStarC_Reflection_V2_Embeddings.e_binding
                                            FStarC_TypeChecker_NBETerm.e_unit
                                            FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                            FStarC_Tactics_V2_Basic.intro
                                            FStarC_Tactics_V2_Basic.intro in
                                        let uu___39 =
                                          let uu___40 =
                                            FStarC_Tactics_InterpFuns.mk_tac_step_1
                                              Prims.int_zero "intros"
                                              FStarC_Syntax_Embeddings.e_int
                                              (FStarC_Syntax_Embeddings.e_list
                                                 FStarC_Reflection_V2_Embeddings.e_binding)
                                              FStarC_TypeChecker_NBETerm.e_int
                                              (FStarC_TypeChecker_NBETerm.e_list
                                                 FStarC_Reflection_V2_NBEEmbeddings.e_binding)
                                              FStarC_Tactics_V2_Basic.intros
                                              FStarC_Tactics_V2_Basic.intros in
                                          let uu___41 =
                                            let uu___42 =
                                              FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                Prims.int_zero "intro_rec"
                                                FStarC_Syntax_Embeddings.e_unit
                                                (FStarC_Syntax_Embeddings.e_tuple2
                                                   FStarC_Reflection_V2_Embeddings.e_binding
                                                   FStarC_Reflection_V2_Embeddings.e_binding)
                                                FStarC_TypeChecker_NBETerm.e_unit
                                                (FStarC_TypeChecker_NBETerm.e_tuple2
                                                   FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                                   FStarC_Reflection_V2_NBEEmbeddings.e_binding)
                                                FStarC_Tactics_V2_Basic.intro_rec
                                                FStarC_Tactics_V2_Basic.intro_rec in
                                            let uu___43 =
                                              let uu___44 =
                                                FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                  Prims.int_zero "norm"
                                                  (FStarC_Syntax_Embeddings.e_list
                                                     FStarC_Syntax_Embeddings.e_norm_step)
                                                  FStarC_Syntax_Embeddings.e_unit
                                                  (FStarC_TypeChecker_NBETerm.e_list
                                                     FStarC_TypeChecker_NBETerm.e_norm_step)
                                                  FStarC_TypeChecker_NBETerm.e_unit
                                                  FStarC_Tactics_V2_Basic.norm
                                                  FStarC_Tactics_V2_Basic.norm in
                                              let uu___45 =
                                                let uu___46 =
                                                  FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                    Prims.int_zero
                                                    "norm_term_env"
                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                    (FStarC_Syntax_Embeddings.e_list
                                                       FStarC_Syntax_Embeddings.e_norm_step)
                                                    uu___0 uu___0
                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                       FStarC_TypeChecker_NBETerm.e_norm_step)
                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                    FStarC_Tactics_V2_Basic.norm_term_env
                                                    FStarC_Tactics_V2_Basic.norm_term_env in
                                                let uu___47 =
                                                  let uu___48 =
                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                      Prims.int_zero
                                                      "norm_binding_type"
                                                      (FStarC_Syntax_Embeddings.e_list
                                                         FStarC_Syntax_Embeddings.e_norm_step)
                                                      FStarC_Reflection_V2_Embeddings.e_binding
                                                      FStarC_Syntax_Embeddings.e_unit
                                                      (FStarC_TypeChecker_NBETerm.e_list
                                                         FStarC_TypeChecker_NBETerm.e_norm_step)
                                                      FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                                      FStarC_TypeChecker_NBETerm.e_unit
                                                      FStarC_Tactics_V2_Basic.norm_binding_type
                                                      FStarC_Tactics_V2_Basic.norm_binding_type in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                        Prims.int_zero
                                                        "rename_to"
                                                        FStarC_Reflection_V2_Embeddings.e_binding
                                                        FStarC_Syntax_Embeddings.e_string
                                                        FStarC_Reflection_V2_Embeddings.e_binding
                                                        FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                                        FStarC_TypeChecker_NBETerm.e_string
                                                        FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                                        FStarC_Tactics_V2_Basic.rename_to
                                                        FStarC_Tactics_V2_Basic.rename_to in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                          Prims.int_zero
                                                          "var_retype"
                                                          FStarC_Reflection_V2_Embeddings.e_binding
                                                          FStarC_Syntax_Embeddings.e_unit
                                                          FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                                          FStarC_TypeChecker_NBETerm.e_unit
                                                          FStarC_Tactics_V2_Basic.var_retype
                                                          FStarC_Tactics_V2_Basic.var_retype in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                            Prims.int_zero
                                                            "revert"
                                                            FStarC_Syntax_Embeddings.e_unit
                                                            FStarC_Syntax_Embeddings.e_unit
                                                            FStarC_TypeChecker_NBETerm.e_unit
                                                            FStarC_TypeChecker_NBETerm.e_unit
                                                            FStarC_Tactics_V2_Basic.revert
                                                            FStarC_Tactics_V2_Basic.revert in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                              Prims.int_zero
                                                              "clear_top"
                                                              FStarC_Syntax_Embeddings.e_unit
                                                              FStarC_Syntax_Embeddings.e_unit
                                                              FStarC_TypeChecker_NBETerm.e_unit
                                                              FStarC_TypeChecker_NBETerm.e_unit
                                                              FStarC_Tactics_V2_Basic.clear_top
                                                              FStarC_Tactics_V2_Basic.clear_top in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                Prims.int_zero
                                                                "clear"
                                                                FStarC_Reflection_V2_Embeddings.e_binding
                                                                FStarC_Syntax_Embeddings.e_unit
                                                                FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                                                FStarC_TypeChecker_NBETerm.e_unit
                                                                FStarC_Tactics_V2_Basic.clear
                                                                FStarC_Tactics_V2_Basic.clear in
                                                            let uu___59 =
                                                              let uu___60 =
                                                                FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                  Prims.int_zero
                                                                  "rewrite"
                                                                  FStarC_Reflection_V2_Embeddings.e_binding
                                                                  FStarC_Syntax_Embeddings.e_unit
                                                                  FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                                                  FStarC_TypeChecker_NBETerm.e_unit
                                                                  FStarC_Tactics_V2_Basic.rewrite
                                                                  FStarC_Tactics_V2_Basic.rewrite in
                                                              let uu___61 =
                                                                let uu___62 =
                                                                  FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "grewrite"
                                                                    uu___0
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.grewrite
                                                                    FStarC_Tactics_V2_Basic.grewrite in
                                                                let uu___63 =
                                                                  let uu___64
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "refine_intro"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.refine_intro
                                                                    FStarC_Tactics_V2_Basic.refine_intro in
                                                                  let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "t_exact"
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.t_exact
                                                                    FStarC_Tactics_V2_Basic.t_exact in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "t_apply"
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.t_apply
                                                                    FStarC_Tactics_V2_Basic.t_apply in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "t_apply_lemma"
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.t_apply_lemma
                                                                    FStarC_Tactics_V2_Basic.t_apply_lemma in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_options"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.set_options
                                                                    FStarC_Tactics_V2_Basic.set_options in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "tcc"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    FStarC_Reflection_V2_Embeddings.e_comp
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_comp
                                                                    FStarC_Tactics_V2_Basic.tcc
                                                                    FStarC_Tactics_V2_Basic.tcc in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "tc"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Tactics_V2_Basic.tc
                                                                    FStarC_Tactics_V2_Basic.tc in
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "unshelve"
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.unshelve
                                                                    FStarC_Tactics_V2_Basic.unshelve in
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Reflection_V2_Embeddings.e_term
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_term
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_Tactics_V2_Basic.unquote
                                                                    (fun
                                                                    uu___81
                                                                    uu___82
                                                                    ->
                                                                    FStarC_Effect.failwith
                                                                    "NBE unquote") in
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "prune"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.prune
                                                                    FStarC_Tactics_V2_Basic.prune in
                                                                    let uu___83
                                                                    =
                                                                    let uu___84
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "addns"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.addns
                                                                    FStarC_Tactics_V2_Basic.addns in
                                                                    let uu___85
                                                                    =
                                                                    let uu___86
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "print"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.print
                                                                    FStarC_Tactics_V2_Basic.print in
                                                                    let uu___87
                                                                    =
                                                                    let uu___88
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "debugging"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Tactics_V2_Basic.debugging
                                                                    FStarC_Tactics_V2_Basic.debugging in
                                                                    let uu___89
                                                                    =
                                                                    let uu___90
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "ide"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Tactics_V2_Basic.ide
                                                                    FStarC_Tactics_V2_Basic.ide in
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dump"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.dump
                                                                    FStarC_Tactics_V2_Basic.dump in
                                                                    let uu___93
                                                                    =
                                                                    let uu___94
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "dump_all"
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.dump_all
                                                                    FStarC_Tactics_V2_Basic.dump_all in
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "dump_uvars_of"
                                                                    FStarC_Tactics_Embedding.e_goal
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Tactics_Embedding.e_goal_nbe
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.dump_uvars_of
                                                                    FStarC_Tactics_V2_Basic.dump_uvars_of in
                                                                    let uu___97
                                                                    =
                                                                    let uu___98
                                                                    =
                                                                    let uu___99
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_1
                                                                    FStarC_Reflection_V2_Embeddings.e_term
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Tactics_Embedding.e_ctrl_flag) in
                                                                    let uu___100
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_thunk
                                                                    FStarC_Syntax_Embeddings.e_unit in
                                                                    let uu___101
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_nbe_1
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_term
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Tactics_Embedding.e_ctrl_flag_nbe) in
                                                                    let uu___102
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStarC_TypeChecker_NBETerm.e_unit in
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStarC_Tactics_Embedding.e_direction
                                                                    uu___99
                                                                    uu___100
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Tactics_Embedding.e_direction_nbe
                                                                    uu___101
                                                                    uu___102
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStarC_Tactics_CtrlRewrite.ctrl_rewrite in
                                                                    let uu___99
                                                                    =
                                                                    let uu___100
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_trefl"
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.t_trefl
                                                                    FStarC_Tactics_V2_Basic.t_trefl in
                                                                    let uu___101
                                                                    =
                                                                    let uu___102
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dup"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.dup
                                                                    FStarC_Tactics_V2_Basic.dup in
                                                                    let uu___103
                                                                    =
                                                                    let uu___104
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "tadmit_t"
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.tadmit_t
                                                                    FStarC_Tactics_V2_Basic.tadmit_t in
                                                                    let uu___105
                                                                    =
                                                                    let uu___106
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "join"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.join
                                                                    FStarC_Tactics_V2_Basic.join in
                                                                    let uu___107
                                                                    =
                                                                    let uu___108
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Reflection_V2_Embeddings.e_fv
                                                                    FStarC_Syntax_Embeddings.e_int))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_fv
                                                                    FStarC_TypeChecker_NBETerm.e_int))
                                                                    FStarC_Tactics_V2_Basic.t_destruct
                                                                    FStarC_Tactics_V2_Basic.t_destruct in
                                                                    let uu___109
                                                                    =
                                                                    let uu___110
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "top_env"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Tactics_V2_Basic.top_env
                                                                    FStarC_Tactics_V2_Basic.top_env in
                                                                    let uu___111
                                                                    =
                                                                    let uu___112
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_int
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_int
                                                                    FStarC_Tactics_V2_Basic.fresh
                                                                    FStarC_Tactics_V2_Basic.fresh in
                                                                    let uu___113
                                                                    =
                                                                    let uu___114
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "curms"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_int
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_int
                                                                    FStarC_Tactics_V2_Basic.curms
                                                                    FStarC_Tactics_V2_Basic.curms in
                                                                    let uu___115
                                                                    =
                                                                    let uu___116
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    uu___0)
                                                                    uu___0
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Tactics_V2_Basic.uvar_env
                                                                    FStarC_Tactics_V2_Basic.uvar_env in
                                                                    let uu___117
                                                                    =
                                                                    let uu___118
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "ghost_uvar_env"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Tactics_V2_Basic.ghost_uvar_env
                                                                    FStarC_Tactics_V2_Basic.ghost_uvar_env in
                                                                    let uu___119
                                                                    =
                                                                    let uu___120
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh_universe_uvar"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    uu___0
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Tactics_V2_Basic.fresh_universe_uvar
                                                                    FStarC_Tactics_V2_Basic.fresh_universe_uvar in
                                                                    let uu___121
                                                                    =
                                                                    let uu___122
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "unify_env"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Tactics_V2_Basic.unify_env
                                                                    FStarC_Tactics_V2_Basic.unify_env in
                                                                    let uu___123
                                                                    =
                                                                    let uu___124
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "unify_guard_env"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Tactics_V2_Basic.unify_guard_env
                                                                    FStarC_Tactics_V2_Basic.unify_guard_env in
                                                                    let uu___125
                                                                    =
                                                                    let uu___126
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "match_env"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Tactics_V2_Basic.match_env
                                                                    FStarC_Tactics_V2_Basic.match_env in
                                                                    let uu___127
                                                                    =
                                                                    let uu___128
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_string_list
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string_list
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_Tactics_V2_Basic.launch_process
                                                                    FStarC_Tactics_V2_Basic.launch_process in
                                                                    let uu___129
                                                                    =
                                                                    let uu___130
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "change"
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.change
                                                                    FStarC_Tactics_V2_Basic.change in
                                                                    let uu___131
                                                                    =
                                                                    let uu___132
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "get_guard_policy"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Tactics_Embedding.e_guard_policy
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStarC_Tactics_V2_Basic.get_guard_policy
                                                                    FStarC_Tactics_V2_Basic.get_guard_policy in
                                                                    let uu___133
                                                                    =
                                                                    let uu___134
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_guard_policy"
                                                                    FStarC_Tactics_Embedding.e_guard_policy
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.set_guard_policy
                                                                    FStarC_Tactics_V2_Basic.set_guard_policy in
                                                                    let uu___135
                                                                    =
                                                                    let uu___136
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "lax_on"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Tactics_V2_Basic.lax_on
                                                                    FStarC_Tactics_V2_Basic.lax_on in
                                                                    let uu___137
                                                                    =
                                                                    let uu___138
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_Tactics_V2_Basic.lget
                                                                    (fun
                                                                    uu___139
                                                                    uu___140
                                                                    ->
                                                                    FStarC_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE") in
                                                                    let uu___139
                                                                    =
                                                                    let uu___140
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "lset"
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.lset
                                                                    (fun
                                                                    uu___141
                                                                    uu___142
                                                                    uu___143
                                                                    ->
                                                                    FStarC_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE") in
                                                                    let uu___141
                                                                    =
                                                                    let uu___142
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_one
                                                                    "set_urgency"
                                                                    FStarC_Syntax_Embeddings.e_int
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_int
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.set_urgency
                                                                    FStarC_Tactics_V2_Basic.set_urgency in
                                                                    let uu___143
                                                                    =
                                                                    let uu___144
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_one
                                                                    "set_dump_on_failure"
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.set_dump_on_failure
                                                                    FStarC_Tactics_V2_Basic.set_dump_on_failure in
                                                                    let uu___145
                                                                    =
                                                                    let uu___146
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_one
                                                                    "t_commute_applied_match"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.t_commute_applied_match
                                                                    FStarC_Tactics_V2_Basic.t_commute_applied_match in
                                                                    let uu___147
                                                                    =
                                                                    let uu___148
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "gather_or_solve_explicit_guards_for_resolved_goals"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.gather_explicit_guards_for_resolved_goals
                                                                    FStarC_Tactics_V2_Basic.gather_explicit_guards_for_resolved_goals in
                                                                    let uu___149
                                                                    =
                                                                    let uu___150
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "string_to_term"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    uu___0
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Tactics_V2_Basic.string_to_term
                                                                    FStarC_Tactics_V2_Basic.string_to_term in
                                                                    let uu___151
                                                                    =
                                                                    let uu___152
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "push_bv_dsenv"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Reflection_V2_Embeddings.e_binding)
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_binding)
                                                                    FStarC_Tactics_V2_Basic.push_bv_dsenv
                                                                    FStarC_Tactics_V2_Basic.push_bv_dsenv in
                                                                    let uu___153
                                                                    =
                                                                    let uu___154
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "term_to_string"
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_Tactics_V2_Basic.term_to_string
                                                                    FStarC_Tactics_V2_Basic.term_to_string in
                                                                    let uu___155
                                                                    =
                                                                    let uu___156
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "comp_to_string"
                                                                    FStarC_Reflection_V2_Embeddings.e_comp
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_comp
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_Tactics_V2_Basic.comp_to_string
                                                                    FStarC_Tactics_V2_Basic.comp_to_string in
                                                                    let uu___157
                                                                    =
                                                                    let uu___158
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "term_to_doc"
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_document
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_document
                                                                    FStarC_Tactics_V2_Basic.term_to_doc
                                                                    FStarC_Tactics_V2_Basic.term_to_doc in
                                                                    let uu___159
                                                                    =
                                                                    let uu___160
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "comp_to_doc"
                                                                    FStarC_Reflection_V2_Embeddings.e_comp
                                                                    FStarC_Syntax_Embeddings.e_document
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_comp
                                                                    FStarC_TypeChecker_NBETerm.e_document
                                                                    FStarC_Tactics_V2_Basic.comp_to_doc
                                                                    FStarC_Tactics_V2_Basic.comp_to_doc in
                                                                    let uu___161
                                                                    =
                                                                    let uu___162
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "range_to_string"
                                                                    FStarC_Syntax_Embeddings.e_range
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_range
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_Tactics_V2_Basic.range_to_string
                                                                    FStarC_Tactics_V2_Basic.range_to_string in
                                                                    let uu___163
                                                                    =
                                                                    let uu___164
                                                                    =
                                                                    let uu___165
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_thunk
                                                                    FStarC_Syntax_Embeddings.e_any in
                                                                    let uu___166
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStarC_TypeChecker_NBETerm.e_any in
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "with_compat_pre_core"
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_int
                                                                    uu___165
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_int
                                                                    uu___166
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    (fun
                                                                    uu___167
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.with_compat_pre_core)
                                                                    (fun
                                                                    uu___167
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.with_compat_pre_core) in
                                                                    let uu___165
                                                                    =
                                                                    let uu___166
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "get_vconfig"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_vconfig
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_vconfig
                                                                    FStarC_Tactics_V2_Basic.get_vconfig
                                                                    FStarC_Tactics_V2_Basic.get_vconfig in
                                                                    let uu___167
                                                                    =
                                                                    let uu___168
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_vconfig"
                                                                    FStarC_Syntax_Embeddings.e_vconfig
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_vconfig
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.set_vconfig
                                                                    FStarC_Tactics_V2_Basic.set_vconfig in
                                                                    let uu___169
                                                                    =
                                                                    let uu___170
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_smt_sync"
                                                                    FStarC_Syntax_Embeddings.e_vconfig
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_vconfig
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.t_smt_sync
                                                                    FStarC_Tactics_V2_Basic.t_smt_sync in
                                                                    let uu___171
                                                                    =
                                                                    let uu___172
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "free_uvars"
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_int)
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_int)
                                                                    FStarC_Tactics_V2_Basic.free_uvars
                                                                    FStarC_Tactics_V2_Basic.free_uvars in
                                                                    let uu___173
                                                                    =
                                                                    let uu___174
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "all_ext_options"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_string))
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string))
                                                                    FStarC_Tactics_V2_Basic.all_ext_options
                                                                    FStarC_Tactics_V2_Basic.all_ext_options in
                                                                    let uu___175
                                                                    =
                                                                    let uu___176
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "ext_getv"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_Tactics_V2_Basic.ext_getv
                                                                    FStarC_Tactics_V2_Basic.ext_getv in
                                                                    let uu___177
                                                                    =
                                                                    let uu___178
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "ext_enabled"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Tactics_V2_Basic.ext_enabled
                                                                    FStarC_Tactics_V2_Basic.ext_enabled in
                                                                    let uu___179
                                                                    =
                                                                    let uu___180
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "ext_getns"
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_string))
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string))
                                                                    FStarC_Tactics_V2_Basic.ext_getns
                                                                    FStarC_Tactics_V2_Basic.ext_getns in
                                                                    let uu___181
                                                                    =
                                                                    let uu___182
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "alloc"
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    (FStarC_Tactics_Embedding.e_tref
                                                                    ())
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    (FStarC_Tactics_Embedding.e_tref_nbe
                                                                    ())
                                                                    (fun
                                                                    uu___183
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.alloc)
                                                                    (fun
                                                                    uu___183
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.alloc) in
                                                                    let uu___183
                                                                    =
                                                                    let uu___184
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "read"
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    (FStarC_Tactics_Embedding.e_tref
                                                                    ())
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    (FStarC_Tactics_Embedding.e_tref_nbe
                                                                    ())
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    (fun
                                                                    uu___185
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.read)
                                                                    (fun
                                                                    uu___185
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.read) in
                                                                    let uu___185
                                                                    =
                                                                    let uu___186
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "write"
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    (FStarC_Tactics_Embedding.e_tref
                                                                    ())
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    (FStarC_Tactics_Embedding.e_tref_nbe
                                                                    ())
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    (fun
                                                                    uu___187
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.write)
                                                                    (fun
                                                                    uu___187
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.write) in
                                                                    let uu___187
                                                                    =
                                                                    let uu___188
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "splice_quals"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Reflection_V2_Embeddings.e_qualifier)
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_qualifiers
                                                                    FStarC_Tactics_V2_Basic.splice_quals
                                                                    FStarC_Tactics_V2_Basic.splice_quals in
                                                                    let uu___189
                                                                    =
                                                                    let uu___190
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "splice_attrs"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    uu___0)
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attributes
                                                                    FStarC_Tactics_V2_Basic.splice_attrs
                                                                    FStarC_Tactics_V2_Basic.splice_attrs in
                                                                    let uu___191
                                                                    =
                                                                    let uu___192
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "is_non_informative"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    FStarC_Syntax_Embeddings.e_unit)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_TypeChecker_NBETerm.e_unit)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_is_non_informative
                                                                    FStarC_Tactics_V2_Basic.refl_is_non_informative in
                                                                    let uu___193
                                                                    =
                                                                    let uu___194
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "check_subtyping"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    FStarC_Syntax_Embeddings.e_unit)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_TypeChecker_NBETerm.e_unit)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_check_subtyping
                                                                    FStarC_Tactics_V2_Basic.refl_check_subtyping in
                                                                    let uu___195
                                                                    =
                                                                    let uu___196
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_5
                                                                    Prims.int_zero
                                                                    "t_check_equiv"
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    FStarC_Syntax_Embeddings.e_unit)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_TypeChecker_NBETerm.e_unit)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.t_refl_check_equiv
                                                                    FStarC_Tactics_V2_Basic.t_refl_check_equiv in
                                                                    let uu___197
                                                                    =
                                                                    let uu___198
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "core_compute_term_type"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Tactics_Embedding.e_tot_or_ghost
                                                                    uu___0))
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Tactics_Embedding.e_tot_or_ghost_nbe
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute))
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_core_compute_term_type
                                                                    FStarC_Tactics_V2_Basic.refl_core_compute_term_type in
                                                                    let uu___199
                                                                    =
                                                                    let uu___200
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "core_check_term"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    FStarC_Tactics_Embedding.e_tot_or_ghost
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    FStarC_Syntax_Embeddings.e_unit)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Tactics_Embedding.e_tot_or_ghost_nbe
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_TypeChecker_NBETerm.e_unit)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_core_check_term
                                                                    FStarC_Tactics_V2_Basic.refl_core_check_term in
                                                                    let uu___201
                                                                    =
                                                                    let uu___202
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "core_check_term_at_type"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    FStarC_Tactics_Embedding.e_tot_or_ghost)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Tactics_Embedding.e_tot_or_ghost_nbe)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_core_check_term_at_type
                                                                    FStarC_Tactics_V2_Basic.refl_core_check_term_at_type in
                                                                    let uu___203
                                                                    =
                                                                    let uu___204
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "tc_term"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Tactics_Embedding.e_tot_or_ghost
                                                                    uu___0)))
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Tactics_Embedding.e_tot_or_ghost_nbe
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)))
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_tc_term
                                                                    FStarC_Tactics_V2_Basic.refl_tc_term in
                                                                    let uu___205
                                                                    =
                                                                    let uu___206
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "universe_of"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    FStarC_Reflection_V2_Embeddings.e_universe)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_universe)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_universe_of
                                                                    FStarC_Tactics_V2_Basic.refl_universe_of in
                                                                    let uu___207
                                                                    =
                                                                    let uu___208
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "check_prop_validity"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    FStarC_Syntax_Embeddings.e_unit)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_TypeChecker_NBETerm.e_unit)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_check_prop_validity
                                                                    FStarC_Tactics_V2_Basic.refl_check_prop_validity in
                                                                    let uu___209
                                                                    =
                                                                    let uu___210
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "check_match_complete"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Reflection_V2_Embeddings.e_pattern)
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Reflection_V2_Embeddings.e_pattern)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Reflection_V2_Embeddings.e_binding))))
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_pattern)
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_pattern)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_binding))))
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_check_match_complete
                                                                    FStarC_Tactics_V2_Basic.refl_check_match_complete in
                                                                    let uu___211
                                                                    =
                                                                    let uu___212
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "instantiate_implicits"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    uu___0)
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    (e_ret_t
                                                                    (FStarC_Syntax_Embeddings.e_tuple3
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Reflection_V2_Embeddings.e_namedv
                                                                    uu___0))
                                                                    uu___0
                                                                    uu___0))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    (nbe_e_ret_t
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple3
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute))
                                                                    FStarC_Tactics_V2_Basic.refl_instantiate_implicits
                                                                    FStarC_Tactics_V2_Basic.refl_instantiate_implicits in
                                                                    let uu___213
                                                                    =
                                                                    let uu___214
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "try_unify"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Reflection_V2_Embeddings.e_namedv
                                                                    FStarC_Reflection_V2_Embeddings.e_term))
                                                                    uu___0
                                                                    uu___0
                                                                    (e_ret_t
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Reflection_V2_Embeddings.e_namedv
                                                                    FStarC_Reflection_V2_Embeddings.e_term)))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_term))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (nbe_e_ret_t
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_term)))
                                                                    FStarC_Tactics_V2_Basic.refl_try_unify
                                                                    FStarC_Tactics_V2_Basic.refl_try_unify in
                                                                    let uu___215
                                                                    =
                                                                    let uu___216
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "maybe_relate_after_unfolding"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    FStarC_Tactics_Embedding.e_unfold_side)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Tactics_Embedding.e_unfold_side_nbe)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_maybe_relate_after_unfolding
                                                                    FStarC_Tactics_V2_Basic.refl_maybe_relate_after_unfolding in
                                                                    let uu___217
                                                                    =
                                                                    let uu___218
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "maybe_unfold_head"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    uu___0)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.refl_maybe_unfold_head
                                                                    FStarC_Tactics_V2_Basic.refl_maybe_unfold_head in
                                                                    let uu___219
                                                                    =
                                                                    let uu___220
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "norm_well_typed_term"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_norm_step)
                                                                    uu___0
                                                                    uu___0
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_norm_step)
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Tactics_V2_Basic.refl_norm_well_typed_term
                                                                    FStarC_Tactics_V2_Basic.refl_norm_well_typed_term in
                                                                    let uu___221
                                                                    =
                                                                    let uu___222
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "push_open_namespace"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Syntax_Embeddings.e_string_list
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_TypeChecker_NBETerm.e_string_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Tactics_V2_Basic.push_open_namespace
                                                                    FStarC_Tactics_V2_Basic.push_open_namespace in
                                                                    let uu___223
                                                                    =
                                                                    let uu___224
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "push_module_abbrev"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    FStarC_Syntax_Embeddings.e_string_list
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    FStarC_TypeChecker_NBETerm.e_string_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Tactics_V2_Basic.push_module_abbrev
                                                                    FStarC_Tactics_V2_Basic.push_module_abbrev in
                                                                    let uu___225
                                                                    =
                                                                    let uu___226
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "resolve_name"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Syntax_Embeddings.e_string_list
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    (FStarC_Syntax_Embeddings.e_either
                                                                    FStarC_Reflection_V2_Embeddings.e_bv
                                                                    FStarC_Reflection_V2_Embeddings.e_fv))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_TypeChecker_NBETerm.e_string_list
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    (FStarC_TypeChecker_NBETerm.e_either
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_bv
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_fv))
                                                                    FStarC_Tactics_V2_Basic.resolve_name
                                                                    FStarC_Tactics_V2_Basic.resolve_name in
                                                                    let uu___227
                                                                    =
                                                                    let uu___228
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "log_issues"
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue)
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue)
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.log_issues
                                                                    FStarC_Tactics_V2_Basic.log_issues in
                                                                    let uu___229
                                                                    =
                                                                    let uu___230
                                                                    =
                                                                    let uu___231
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_thunk
                                                                    FStarC_Syntax_Embeddings.e_unit in
                                                                    let uu___232
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStarC_TypeChecker_NBETerm.e_unit in
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "call_subtac"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___231
                                                                    FStarC_Reflection_V2_Embeddings.e_universe
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    uu___0)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    uu___232
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_universe
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.call_subtac
                                                                    FStarC_Tactics_V2_Basic.call_subtac in
                                                                    let uu___231
                                                                    =
                                                                    let uu___232
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "call_subtac_tm"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    FStarC_Reflection_V2_Embeddings.e_universe
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    uu___0)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_universe
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.call_subtac_tm
                                                                    FStarC_Tactics_V2_Basic.call_subtac_tm in
                                                                    let uu___233
                                                                    =
                                                                    let uu___234
                                                                    =
                                                                    let uu___235
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_thunk
                                                                    FStarC_Syntax_Embeddings.e_any in
                                                                    let uu___236
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStarC_TypeChecker_NBETerm.e_any in
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_one
                                                                    "stats_record"
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    uu___235
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    uu___236
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_Tactics_V2_Basic.stats_record
                                                                    FStarC_Tactics_V2_Basic.stats_record in
                                                                    let uu___235
                                                                    =
                                                                    let uu___236
                                                                    =
                                                                    let uu___237
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_thunk
                                                                    FStarC_Syntax_Embeddings.e_any in
                                                                    let uu___238
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStarC_TypeChecker_NBETerm.e_any in
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_one
                                                                    "with_error_context"
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_string
                                                                    uu___237
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_string
                                                                    uu___238
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_Tactics_V2_Basic.with_error_context
                                                                    FStarC_Tactics_V2_Basic.with_error_context in
                                                                    [uu___236] in
                                                                    uu___234
                                                                    ::
                                                                    uu___235 in
                                                                    uu___232
                                                                    ::
                                                                    uu___233 in
                                                                    uu___230
                                                                    ::
                                                                    uu___231 in
                                                                    uu___228
                                                                    ::
                                                                    uu___229 in
                                                                    uu___226
                                                                    ::
                                                                    uu___227 in
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
                          uu___24 :: uu___25 in
                        uu___22 :: uu___23 in
                      uu___20 :: uu___21 in
                    uu___18 :: uu___19 in
                  uu___16 :: uu___17 in
                uu___14 :: uu___15 in
              uu___12 :: uu___13 in
            uu___10 :: uu___11 in
          uu___8 :: uu___9 in
        uu___6 :: uu___7 in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1
