open Prims
let solve : 'a . 'a -> 'a = fun ev -> ev
let (uu___0 :
  FStarC_Syntax_Syntax.term FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Reflection_V2_Embeddings.e_term
let unseal :
  'uuuuu 'a .
    'uuuuu -> 'a FStarC_Compiler_Sealed.sealed -> 'a FStarC_Tactics_Monad.tac
  =
  fun uu___1 ->
    fun uu___ ->
      (fun _typ ->
         fun x ->
           Obj.magic
             (FStarC_Class_Monad.return FStarC_Tactics_Monad.monad_tac ()
                (Obj.magic (FStarC_Compiler_Sealed.unseal x)))) uu___1 uu___
let (unseal_step : FStarC_TypeChecker_Primops_Base.primitive_step) =
  let s =
    FStarC_Tactics_InterpFuns.mk_tac_step_2 Prims.int_one "unseal"
      FStarC_Syntax_Embeddings.e_any
      (FStarC_Syntax_Embeddings.e_sealed FStarC_Syntax_Embeddings.e_any)
      FStarC_Syntax_Embeddings.e_any FStarC_TypeChecker_NBETerm.e_any
      (FStarC_TypeChecker_NBETerm.e_sealed FStarC_TypeChecker_NBETerm.e_any)
      FStarC_TypeChecker_NBETerm.e_any unseal unseal in
  {
    FStarC_TypeChecker_Primops_Base.name = FStarC_Parser_Const.unseal_lid;
    FStarC_TypeChecker_Primops_Base.arity =
      (s.FStarC_TypeChecker_Primops_Base.arity);
    FStarC_TypeChecker_Primops_Base.univ_arity =
      (s.FStarC_TypeChecker_Primops_Base.univ_arity);
    FStarC_TypeChecker_Primops_Base.auto_reflect =
      (s.FStarC_TypeChecker_Primops_Base.auto_reflect);
    FStarC_TypeChecker_Primops_Base.strong_reduction_ok =
      (s.FStarC_TypeChecker_Primops_Base.strong_reduction_ok);
    FStarC_TypeChecker_Primops_Base.requires_binder_substitution =
      (s.FStarC_TypeChecker_Primops_Base.requires_binder_substitution);
    FStarC_TypeChecker_Primops_Base.renorm_after =
      (s.FStarC_TypeChecker_Primops_Base.renorm_after);
    FStarC_TypeChecker_Primops_Base.interpretation =
      (s.FStarC_TypeChecker_Primops_Base.interpretation);
    FStarC_TypeChecker_Primops_Base.interpretation_nbe =
      (s.FStarC_TypeChecker_Primops_Base.interpretation_nbe)
  }
let e_ret_t :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      ('a FStar_Pervasives_Native.option * FStarC_Tactics_V2_Basic.issues)
        FStarC_Syntax_Embeddings_Base.embedding
  =
  fun d ->
    solve
      (FStarC_Syntax_Embeddings.e_tuple2
         (FStarC_Syntax_Embeddings.e_option d)
         (FStarC_Syntax_Embeddings.e_list FStarC_Syntax_Embeddings.e_issue))
let nbe_e_ret_t :
  'a .
    'a FStarC_TypeChecker_NBETerm.embedding ->
      ('a FStar_Pervasives_Native.option * FStarC_Tactics_V2_Basic.issues)
        FStarC_TypeChecker_NBETerm.embedding
  =
  fun d ->
    solve
      (FStarC_TypeChecker_NBETerm.e_tuple2
         (FStarC_TypeChecker_NBETerm.e_option d)
         (FStarC_TypeChecker_NBETerm.e_list
            FStarC_TypeChecker_NBETerm.e_issue))
let (ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
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
                            let uu___25 =
                              FStarC_Tactics_InterpFuns.mk_tac_step_1
                                Prims.int_zero "compress" uu___0 uu___0
                                FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                FStarC_Tactics_V2_Basic.compress
                                FStarC_Tactics_V2_Basic.compress in
                            let uu___26 =
                              let uu___27 =
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
                              let uu___28 =
                                let uu___29 =
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
                                let uu___30 =
                                  let uu___31 =
                                    let uu___32 =
                                      FStarC_Tactics_Interpreter.e_tactic_thunk
                                        FStarC_Syntax_Embeddings.e_any in
                                    let uu___33 =
                                      FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                        FStarC_TypeChecker_NBETerm.e_any in
                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                      Prims.int_one "catch"
                                      FStarC_Syntax_Embeddings.e_any uu___32
                                      (FStarC_Syntax_Embeddings.e_either
                                         FStarC_Tactics_Embedding.e_exn
                                         FStarC_Syntax_Embeddings.e_any)
                                      FStarC_TypeChecker_NBETerm.e_any
                                      uu___33
                                      (FStarC_TypeChecker_NBETerm.e_either
                                         FStarC_Tactics_Embedding.e_exn_nbe
                                         FStarC_TypeChecker_NBETerm.e_any)
                                      (fun uu___34 ->
                                         FStarC_Tactics_Monad.catch)
                                      (fun uu___34 ->
                                         FStarC_Tactics_Monad.catch) in
                                  let uu___32 =
                                    let uu___33 =
                                      let uu___34 =
                                        FStarC_Tactics_Interpreter.e_tactic_thunk
                                          FStarC_Syntax_Embeddings.e_any in
                                      let uu___35 =
                                        FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                          FStarC_TypeChecker_NBETerm.e_any in
                                      FStarC_Tactics_InterpFuns.mk_tac_step_2
                                        Prims.int_one "recover"
                                        FStarC_Syntax_Embeddings.e_any
                                        uu___34
                                        (FStarC_Syntax_Embeddings.e_either
                                           FStarC_Tactics_Embedding.e_exn
                                           FStarC_Syntax_Embeddings.e_any)
                                        FStarC_TypeChecker_NBETerm.e_any
                                        uu___35
                                        (FStarC_TypeChecker_NBETerm.e_either
                                           FStarC_Tactics_Embedding.e_exn_nbe
                                           FStarC_TypeChecker_NBETerm.e_any)
                                        (fun uu___36 ->
                                           FStarC_Tactics_Monad.recover)
                                        (fun uu___36 ->
                                           FStarC_Tactics_Monad.recover) in
                                    let uu___34 =
                                      let uu___35 =
                                        FStarC_Tactics_InterpFuns.mk_tac_step_1
                                          Prims.int_zero "intro"
                                          FStarC_Syntax_Embeddings.e_unit
                                          FStarC_Reflection_V2_Embeddings.e_binding
                                          FStarC_TypeChecker_NBETerm.e_unit
                                          FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                          FStarC_Tactics_V2_Basic.intro
                                          FStarC_Tactics_V2_Basic.intro in
                                      let uu___36 =
                                        let uu___37 =
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
                                        let uu___38 =
                                          let uu___39 =
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
                                          let uu___40 =
                                            let uu___41 =
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
                                            let uu___42 =
                                              let uu___43 =
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
                                              let uu___44 =
                                                let uu___45 =
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
                                                let uu___46 =
                                                  let uu___47 =
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
                                                  let uu___48 =
                                                    let uu___49 =
                                                      FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                        Prims.int_zero
                                                        "var_retype"
                                                        FStarC_Reflection_V2_Embeddings.e_binding
                                                        FStarC_Syntax_Embeddings.e_unit
                                                        FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                                        FStarC_TypeChecker_NBETerm.e_unit
                                                        FStarC_Tactics_V2_Basic.var_retype
                                                        FStarC_Tactics_V2_Basic.var_retype in
                                                    let uu___50 =
                                                      let uu___51 =
                                                        FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                          Prims.int_zero
                                                          "revert"
                                                          FStarC_Syntax_Embeddings.e_unit
                                                          FStarC_Syntax_Embeddings.e_unit
                                                          FStarC_TypeChecker_NBETerm.e_unit
                                                          FStarC_TypeChecker_NBETerm.e_unit
                                                          FStarC_Tactics_V2_Basic.revert
                                                          FStarC_Tactics_V2_Basic.revert in
                                                      let uu___52 =
                                                        let uu___53 =
                                                          FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                            Prims.int_zero
                                                            "clear_top"
                                                            FStarC_Syntax_Embeddings.e_unit
                                                            FStarC_Syntax_Embeddings.e_unit
                                                            FStarC_TypeChecker_NBETerm.e_unit
                                                            FStarC_TypeChecker_NBETerm.e_unit
                                                            FStarC_Tactics_V2_Basic.clear_top
                                                            FStarC_Tactics_V2_Basic.clear_top in
                                                        let uu___54 =
                                                          let uu___55 =
                                                            FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                              Prims.int_zero
                                                              "clear"
                                                              FStarC_Reflection_V2_Embeddings.e_binding
                                                              FStarC_Syntax_Embeddings.e_unit
                                                              FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                                              FStarC_TypeChecker_NBETerm.e_unit
                                                              FStarC_Tactics_V2_Basic.clear
                                                              FStarC_Tactics_V2_Basic.clear in
                                                          let uu___56 =
                                                            let uu___57 =
                                                              FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                Prims.int_zero
                                                                "rewrite"
                                                                FStarC_Reflection_V2_Embeddings.e_binding
                                                                FStarC_Syntax_Embeddings.e_unit
                                                                FStarC_Reflection_V2_NBEEmbeddings.e_binding
                                                                FStarC_TypeChecker_NBETerm.e_unit
                                                                FStarC_Tactics_V2_Basic.rewrite
                                                                FStarC_Tactics_V2_Basic.rewrite in
                                                            let uu___58 =
                                                              let uu___59 =
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
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  FStarC_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "refine_intro"
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_V2_Basic.refine_intro
                                                                    FStarC_Tactics_V2_Basic.refine_intro in
                                                                let uu___62 =
                                                                  let uu___63
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
                                                                  let uu___64
                                                                    =
                                                                    let uu___65
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
                                                                    let uu___66
                                                                    =
                                                                    let uu___67
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
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
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
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
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
                                                                    let uu___72
                                                                    =
                                                                    let uu___73
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
                                                                    let uu___74
                                                                    =
                                                                    let uu___75
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
                                                                    let uu___76
                                                                    =
                                                                    let uu___77
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
                                                                    uu___78
                                                                    ->
                                                                    fun
                                                                    uu___79
                                                                    ->
                                                                    failwith
                                                                    "NBE unquote") in
                                                                    let uu___78
                                                                    =
                                                                    let uu___79
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
                                                                    let uu___80
                                                                    =
                                                                    let uu___81
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
                                                                    let uu___82
                                                                    =
                                                                    let uu___83
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
                                                                    let uu___84
                                                                    =
                                                                    let uu___85
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
                                                                    let uu___86
                                                                    =
                                                                    let uu___87
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
                                                                    let uu___88
                                                                    =
                                                                    let uu___89
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
                                                                    let uu___90
                                                                    =
                                                                    let uu___91
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
                                                                    let uu___92
                                                                    =
                                                                    let uu___93
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
                                                                    let uu___94
                                                                    =
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_1
                                                                    FStarC_Reflection_V2_Embeddings.e_term
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Tactics_Embedding.e_ctrl_flag) in
                                                                    let uu___97
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_thunk
                                                                    FStarC_Syntax_Embeddings.e_unit in
                                                                    let uu___98
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_nbe_1
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_term
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Tactics_Embedding.e_ctrl_flag_nbe) in
                                                                    let uu___99
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStarC_TypeChecker_NBETerm.e_unit in
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStarC_Tactics_Embedding.e_direction
                                                                    uu___96
                                                                    uu___97
                                                                    FStarC_Syntax_Embeddings.e_unit
                                                                    FStarC_Tactics_Embedding.e_direction_nbe
                                                                    uu___98
                                                                    uu___99
                                                                    FStarC_TypeChecker_NBETerm.e_unit
                                                                    FStarC_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStarC_Tactics_CtrlRewrite.ctrl_rewrite in
                                                                    let uu___96
                                                                    =
                                                                    let uu___97
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
                                                                    let uu___98
                                                                    =
                                                                    let uu___99
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
                                                                    let uu___100
                                                                    =
                                                                    let uu___101
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
                                                                    let uu___102
                                                                    =
                                                                    let uu___103
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
                                                                    let uu___104
                                                                    =
                                                                    let uu___105
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
                                                                    let uu___106
                                                                    =
                                                                    let uu___107
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
                                                                    let uu___108
                                                                    =
                                                                    let uu___109
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
                                                                    let uu___110
                                                                    =
                                                                    let uu___111
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
                                                                    let uu___112
                                                                    =
                                                                    let uu___113
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
                                                                    let uu___114
                                                                    =
                                                                    let uu___115
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
                                                                    let uu___116
                                                                    =
                                                                    let uu___117
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
                                                                    let uu___118
                                                                    =
                                                                    let uu___119
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
                                                                    let uu___120
                                                                    =
                                                                    let uu___121
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
                                                                    let uu___122
                                                                    =
                                                                    let uu___123
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
                                                                    let uu___124
                                                                    =
                                                                    let uu___125
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
                                                                    let uu___126
                                                                    =
                                                                    let uu___127
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
                                                                    let uu___128
                                                                    =
                                                                    let uu___129
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
                                                                    let uu___130
                                                                    =
                                                                    let uu___131
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
                                                                    let uu___132
                                                                    =
                                                                    let uu___133
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
                                                                    let uu___134
                                                                    =
                                                                    let uu___135
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
                                                                    uu___136
                                                                    ->
                                                                    fun
                                                                    uu___137
                                                                    ->
                                                                    FStarC_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE") in
                                                                    let uu___136
                                                                    =
                                                                    let uu___137
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
                                                                    uu___138
                                                                    ->
                                                                    fun
                                                                    uu___139
                                                                    ->
                                                                    fun
                                                                    uu___140
                                                                    ->
                                                                    FStarC_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE") in
                                                                    let uu___138
                                                                    =
                                                                    let uu___139
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
                                                                    let uu___140
                                                                    =
                                                                    let uu___141
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
                                                                    let uu___142
                                                                    =
                                                                    let uu___143
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
                                                                    let uu___144
                                                                    =
                                                                    let uu___145
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
                                                                    let uu___146
                                                                    =
                                                                    let uu___147
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
                                                                    let uu___148
                                                                    =
                                                                    let uu___149
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
                                                                    let uu___150
                                                                    =
                                                                    let uu___151
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
                                                                    let uu___152
                                                                    =
                                                                    let uu___153
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
                                                                    let uu___154
                                                                    =
                                                                    let uu___155
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
                                                                    let uu___156
                                                                    =
                                                                    let uu___157
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
                                                                    let uu___158
                                                                    =
                                                                    let uu___159
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
                                                                    let uu___160
                                                                    =
                                                                    let uu___161
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "term_eq_old"
                                                                    uu___0
                                                                    uu___0
                                                                    FStarC_Syntax_Embeddings.e_bool
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_TypeChecker_NBETerm.e_bool
                                                                    FStarC_Tactics_V2_Basic.term_eq_old
                                                                    FStarC_Tactics_V2_Basic.term_eq_old in
                                                                    let uu___162
                                                                    =
                                                                    let uu___163
                                                                    =
                                                                    let uu___164
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_thunk
                                                                    FStarC_Syntax_Embeddings.e_any in
                                                                    let uu___165
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStarC_TypeChecker_NBETerm.e_any in
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "with_compat_pre_core"
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_Syntax_Embeddings.e_int
                                                                    uu___164
                                                                    FStarC_Syntax_Embeddings.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    FStarC_TypeChecker_NBETerm.e_int
                                                                    uu___165
                                                                    FStarC_TypeChecker_NBETerm.e_any
                                                                    (fun
                                                                    uu___166
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.with_compat_pre_core)
                                                                    (fun
                                                                    uu___166
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.with_compat_pre_core) in
                                                                    let uu___164
                                                                    =
                                                                    let uu___165
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
                                                                    let uu___166
                                                                    =
                                                                    let uu___167
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
                                                                    let uu___168
                                                                    =
                                                                    let uu___169
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
                                                                    let uu___170
                                                                    =
                                                                    let uu___171
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
                                                                    let uu___172
                                                                    =
                                                                    let uu___173
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
                                                                    let uu___174
                                                                    =
                                                                    let uu___175
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
                                                                    let uu___176
                                                                    =
                                                                    let uu___177
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
                                                                    let uu___178
                                                                    =
                                                                    let uu___179
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
                                                                    uu___180
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.alloc)
                                                                    (fun
                                                                    uu___180
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.alloc) in
                                                                    let uu___180
                                                                    =
                                                                    let uu___181
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
                                                                    uu___182
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.read)
                                                                    (fun
                                                                    uu___182
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.read) in
                                                                    let uu___182
                                                                    =
                                                                    let uu___183
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
                                                                    uu___184
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.write)
                                                                    (fun
                                                                    uu___184
                                                                    ->
                                                                    FStarC_Tactics_V2_Basic.write) in
                                                                    let uu___184
                                                                    =
                                                                    let uu___185
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
                                                                    let uu___186
                                                                    =
                                                                    let uu___187
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
                                                                    let uu___188
                                                                    =
                                                                    let uu___189
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
                                                                    let uu___190
                                                                    =
                                                                    let uu___191
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
                                                                    let uu___192
                                                                    =
                                                                    let uu___193
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
                                                                    let uu___194
                                                                    =
                                                                    let uu___195
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
                                                                    let uu___196
                                                                    =
                                                                    let uu___197
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
                                                                    let uu___198
                                                                    =
                                                                    let uu___199
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
                                                                    let uu___200
                                                                    =
                                                                    let uu___201
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
                                                                    let uu___202
                                                                    =
                                                                    let uu___203
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "check_match_complete"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Reflection_V2_Embeddings.e_pattern)
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Reflection_V2_Embeddings.e_pattern)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Reflection_V2_Embeddings.e_binding))))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_pattern)
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_pattern)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_binding))))
                                                                    FStarC_Tactics_V2_Basic.refl_check_match_complete
                                                                    FStarC_Tactics_V2_Basic.refl_check_match_complete in
                                                                    let uu___204
                                                                    =
                                                                    let uu___205
                                                                    =
                                                                    let uu___206
                                                                    =
                                                                    e_ret_t
                                                                    (FStarC_Syntax_Embeddings.e_tuple3
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Reflection_V2_Embeddings.e_namedv
                                                                    (solve
                                                                    uu___0)))
                                                                    (solve
                                                                    uu___0)
                                                                    (solve
                                                                    uu___0)) in
                                                                    let uu___207
                                                                    =
                                                                    nbe_e_ret_t
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple3
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                                                                    (solve
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)))
                                                                    (solve
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    (solve
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)) in
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "instantiate_implicits"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    uu___0)
                                                                    uu___206
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    uu___207
                                                                    FStarC_Tactics_V2_Basic.refl_instantiate_implicits
                                                                    FStarC_Tactics_V2_Basic.refl_instantiate_implicits in
                                                                    let uu___206
                                                                    =
                                                                    let uu___207
                                                                    =
                                                                    let uu___208
                                                                    =
                                                                    e_ret_t
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    FStarC_Reflection_V2_Embeddings.e_namedv
                                                                    FStarC_Reflection_V2_Embeddings.e_term)) in
                                                                    let uu___209
                                                                    =
                                                                    nbe_e_ret_t
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_term)) in
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
                                                                    uu___208
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_namedv
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_term))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    uu___209
                                                                    FStarC_Tactics_V2_Basic.refl_try_unify
                                                                    FStarC_Tactics_V2_Basic.refl_try_unify in
                                                                    let uu___208
                                                                    =
                                                                    let uu___209
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
                                                                    let uu___210
                                                                    =
                                                                    let uu___211
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
                                                                    let uu___212
                                                                    =
                                                                    let uu___213
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
                                                                    let uu___214
                                                                    =
                                                                    let uu___215
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
                                                                    let uu___216
                                                                    =
                                                                    let uu___217
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
                                                                    let uu___218
                                                                    =
                                                                    let uu___219
                                                                    =
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "resolve_name"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    FStarC_Syntax_Embeddings.e_string_list
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    (FStarC_Syntax_Embeddings.e_either
                                                                    FStarC_Reflection_V2_Embeddings.e_bv
                                                                    (solve
                                                                    FStarC_Reflection_V2_Embeddings.e_fv)))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStarC_TypeChecker_NBETerm.e_string_list
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    (FStarC_TypeChecker_NBETerm.e_either
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_bv
                                                                    (solve
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_fv)))
                                                                    FStarC_Tactics_V2_Basic.resolve_name
                                                                    FStarC_Tactics_V2_Basic.resolve_name in
                                                                    let uu___220
                                                                    =
                                                                    let uu___221
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
                                                                    let uu___222
                                                                    =
                                                                    let uu___223
                                                                    =
                                                                    let uu___224
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_thunk
                                                                    FStarC_Syntax_Embeddings.e_unit in
                                                                    let uu___225
                                                                    =
                                                                    FStarC_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStarC_TypeChecker_NBETerm.e_unit in
                                                                    FStarC_Tactics_InterpFuns.mk_tac_step_4
                                                                    Prims.int_zero
                                                                    "call_subtac"
                                                                    FStarC_Reflection_V2_Embeddings.e_env
                                                                    uu___224
                                                                    FStarC_Reflection_V2_Embeddings.e_universe
                                                                    uu___0
                                                                    (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_option
                                                                    uu___0)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    FStarC_Syntax_Embeddings.e_issue))
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_env
                                                                    uu___225
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_universe
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute
                                                                    (FStarC_TypeChecker_NBETerm.e_tuple2
                                                                    (FStarC_TypeChecker_NBETerm.e_option
                                                                    FStarC_Reflection_V2_NBEEmbeddings.e_attribute)
                                                                    (FStarC_TypeChecker_NBETerm.e_list
                                                                    FStarC_TypeChecker_NBETerm.e_issue))
                                                                    FStarC_Tactics_V2_Basic.call_subtac
                                                                    FStarC_Tactics_V2_Basic.call_subtac in
                                                                    let uu___224
                                                                    =
                                                                    let uu___225
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
                                                                    [uu___225] in
                                                                    uu___223
                                                                    ::
                                                                    uu___224 in
                                                                    uu___221
                                                                    ::
                                                                    uu___222 in
                                                                    uu___219
                                                                    ::
                                                                    uu___220 in
                                                                    uu___217
                                                                    ::
                                                                    uu___218 in
                                                                    uu___215
                                                                    ::
                                                                    uu___216 in
                                                                    uu___213
                                                                    ::
                                                                    uu___214 in
                                                                    uu___211
                                                                    ::
                                                                    uu___212 in
                                                                    uu___209
                                                                    ::
                                                                    uu___210 in
                                                                    uu___207
                                                                    ::
                                                                    uu___208 in
                                                                    uu___205
                                                                    ::
                                                                    uu___206 in
                                                                    uu___203
                                                                    ::
                                                                    uu___204 in
                                                                    uu___201
                                                                    ::
                                                                    uu___202 in
                                                                    uu___199
                                                                    ::
                                                                    uu___200 in
                                                                    uu___197
                                                                    ::
                                                                    uu___198 in
                                                                    uu___195
                                                                    ::
                                                                    uu___196 in
                                                                    uu___193
                                                                    ::
                                                                    uu___194 in
                                                                    uu___191
                                                                    ::
                                                                    uu___192 in
                                                                    uu___189
                                                                    ::
                                                                    uu___190 in
                                                                    uu___187
                                                                    ::
                                                                    uu___188 in
                                                                    uu___185
                                                                    ::
                                                                    uu___186 in
                                                                    uu___183
                                                                    ::
                                                                    uu___184 in
                                                                    uu___181
                                                                    ::
                                                                    uu___182 in
                                                                    uu___179
                                                                    ::
                                                                    uu___180 in
                                                                    uu___177
                                                                    ::
                                                                    uu___178 in
                                                                    uu___175
                                                                    ::
                                                                    uu___176 in
                                                                    uu___173
                                                                    ::
                                                                    uu___174 in
                                                                    uu___171
                                                                    ::
                                                                    uu___172 in
                                                                    uu___169
                                                                    ::
                                                                    uu___170 in
                                                                    uu___167
                                                                    ::
                                                                    uu___168 in
                                                                    uu___165
                                                                    ::
                                                                    uu___166 in
                                                                    uu___163
                                                                    ::
                                                                    uu___164 in
                                                                    uu___161
                                                                    ::
                                                                    uu___162 in
                                                                    uu___159
                                                                    ::
                                                                    uu___160 in
                                                                    uu___157
                                                                    ::
                                                                    uu___158 in
                                                                    uu___155
                                                                    ::
                                                                    uu___156 in
                                                                    uu___153
                                                                    ::
                                                                    uu___154 in
                                                                    uu___151
                                                                    ::
                                                                    uu___152 in
                                                                    uu___149
                                                                    ::
                                                                    uu___150 in
                                                                    uu___147
                                                                    ::
                                                                    uu___148 in
                                                                    uu___145
                                                                    ::
                                                                    uu___146 in
                                                                    uu___143
                                                                    ::
                                                                    uu___144 in
                                                                    uu___141
                                                                    ::
                                                                    uu___142 in
                                                                    uu___139
                                                                    ::
                                                                    uu___140 in
                                                                    uu___137
                                                                    ::
                                                                    uu___138 in
                                                                    uu___135
                                                                    ::
                                                                    uu___136 in
                                                                    uu___133
                                                                    ::
                                                                    uu___134 in
                                                                    uu___131
                                                                    ::
                                                                    uu___132 in
                                                                    uu___129
                                                                    ::
                                                                    uu___130 in
                                                                    uu___127
                                                                    ::
                                                                    uu___128 in
                                                                    uu___125
                                                                    ::
                                                                    uu___126 in
                                                                    uu___123
                                                                    ::
                                                                    uu___124 in
                                                                    uu___121
                                                                    ::
                                                                    uu___122 in
                                                                    uu___119
                                                                    ::
                                                                    uu___120 in
                                                                    uu___117
                                                                    ::
                                                                    uu___118 in
                                                                    uu___115
                                                                    ::
                                                                    uu___116 in
                                                                    uu___113
                                                                    ::
                                                                    uu___114 in
                                                                    uu___111
                                                                    ::
                                                                    uu___112 in
                                                                    uu___109
                                                                    ::
                                                                    uu___110 in
                                                                    uu___107
                                                                    ::
                                                                    uu___108 in
                                                                    uu___105
                                                                    ::
                                                                    uu___106 in
                                                                    uu___103
                                                                    ::
                                                                    uu___104 in
                                                                    uu___101
                                                                    ::
                                                                    uu___102 in
                                                                    uu___99
                                                                    ::
                                                                    uu___100 in
                                                                    uu___97
                                                                    ::
                                                                    uu___98 in
                                                                    uu___95
                                                                    ::
                                                                    uu___96 in
                                                                    uu___93
                                                                    ::
                                                                    uu___94 in
                                                                    uu___91
                                                                    ::
                                                                    uu___92 in
                                                                    uu___89
                                                                    ::
                                                                    uu___90 in
                                                                    uu___87
                                                                    ::
                                                                    uu___88 in
                                                                    uu___85
                                                                    ::
                                                                    uu___86 in
                                                                    uu___83
                                                                    ::
                                                                    uu___84 in
                                                                    uu___81
                                                                    ::
                                                                    uu___82 in
                                                                    uu___79
                                                                    ::
                                                                    uu___80 in
                                                                    uu___77
                                                                    ::
                                                                    uu___78 in
                                                                    uu___75
                                                                    ::
                                                                    uu___76 in
                                                                    uu___73
                                                                    ::
                                                                    uu___74 in
                                                                    uu___71
                                                                    ::
                                                                    uu___72 in
                                                                    uu___69
                                                                    ::
                                                                    uu___70 in
                                                                    uu___67
                                                                    ::
                                                                    uu___68 in
                                                                    uu___65
                                                                    ::
                                                                    uu___66 in
                                                                  uu___63 ::
                                                                    uu___64 in
                                                                uu___61 ::
                                                                  uu___62 in
                                                              uu___59 ::
                                                                uu___60 in
                                                            uu___57 ::
                                                              uu___58 in
                                                          uu___55 :: uu___56 in
                                                        uu___53 :: uu___54 in
                                                      uu___51 :: uu___52 in
                                                    uu___49 :: uu___50 in
                                                  uu___47 :: uu___48 in
                                                uu___45 :: uu___46 in
                                              uu___43 :: uu___44 in
                                            uu___41 :: uu___42 in
                                          uu___39 :: uu___40 in
                                        uu___37 :: uu___38 in
                                      uu___35 :: uu___36 in
                                    uu___33 :: uu___34 in
                                  uu___31 :: uu___32 in
                                uu___29 :: uu___30 in
                              uu___27 :: uu___28 in
                            uu___25 :: uu___26 in
                          unseal_step :: uu___24 in
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