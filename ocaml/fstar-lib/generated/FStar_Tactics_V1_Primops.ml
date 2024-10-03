open Prims
let solve : 'a . 'a -> 'a = fun ev -> ev
let (uu___0 :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V1_Embeddings.e_term
let (fix_module :
  FStar_TypeChecker_Primops_Base.primitive_step ->
    FStar_TypeChecker_Primops_Base.primitive_step)
  =
  fun ps ->
    let p = FStar_Ident.path_of_lid ps.FStar_TypeChecker_Primops_Base.name in
    let uu___ =
      FStar_Compiler_Path.is_under
        (FStar_Class_Ord.ord_eq FStar_Class_Ord.ord_string) p
        ["FStar"; "Stubs"; "Tactics"; "V2"; "Builtins"] in
    if uu___
    then
      let p' =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Compiler_List.tl p in
                FStar_Compiler_List.tl uu___5 in
              FStar_Compiler_List.tl uu___4 in
            FStar_Compiler_List.tl uu___3 in
          FStar_Compiler_List.tl uu___2 in
        FStar_Compiler_List.op_At
          ["FStar"; "Stubs"; "Tactics"; "V1"; "Builtins"] uu___1 in
      let uu___1 =
        let uu___2 =
          FStar_Class_HasRange.pos FStar_Ident.hasrange_lident
            ps.FStar_TypeChecker_Primops_Base.name in
        FStar_Ident.lid_of_path p' uu___2 in
      {
        FStar_TypeChecker_Primops_Base.name = uu___1;
        FStar_TypeChecker_Primops_Base.arity =
          (ps.FStar_TypeChecker_Primops_Base.arity);
        FStar_TypeChecker_Primops_Base.univ_arity =
          (ps.FStar_TypeChecker_Primops_Base.univ_arity);
        FStar_TypeChecker_Primops_Base.auto_reflect =
          (ps.FStar_TypeChecker_Primops_Base.auto_reflect);
        FStar_TypeChecker_Primops_Base.strong_reduction_ok =
          (ps.FStar_TypeChecker_Primops_Base.strong_reduction_ok);
        FStar_TypeChecker_Primops_Base.requires_binder_substitution =
          (ps.FStar_TypeChecker_Primops_Base.requires_binder_substitution);
        FStar_TypeChecker_Primops_Base.renorm_after =
          (ps.FStar_TypeChecker_Primops_Base.renorm_after);
        FStar_TypeChecker_Primops_Base.interpretation =
          (ps.FStar_TypeChecker_Primops_Base.interpretation);
        FStar_TypeChecker_Primops_Base.interpretation_nbe =
          (ps.FStar_TypeChecker_Primops_Base.interpretation_nbe)
      }
    else FStar_Compiler_Effect.failwith "huh?"
let (ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    let uu___1 =
      FStar_Tactics_InterpFuns.mk_tac_step_1 Prims.int_zero "set_goals"
        (FStar_Syntax_Embeddings.e_list FStar_Tactics_Embedding.e_goal)
        FStar_Syntax_Embeddings.e_unit
        (FStar_TypeChecker_NBETerm.e_list FStar_Tactics_Embedding.e_goal_nbe)
        FStar_TypeChecker_NBETerm.e_unit FStar_Tactics_Monad.set_goals
        FStar_Tactics_Monad.set_goals in
    let uu___2 =
      let uu___3 =
        FStar_Tactics_InterpFuns.mk_tac_step_1 Prims.int_zero "set_smt_goals"
          (FStar_Syntax_Embeddings.e_list FStar_Tactics_Embedding.e_goal)
          FStar_Syntax_Embeddings.e_unit
          (FStar_TypeChecker_NBETerm.e_list
             FStar_Tactics_Embedding.e_goal_nbe)
          FStar_TypeChecker_NBETerm.e_unit FStar_Tactics_Monad.set_smt_goals
          FStar_Tactics_Monad.set_smt_goals in
      let uu___4 =
        let uu___5 =
          let uu___6 =
            FStar_Tactics_Interpreter.e_tactic_thunk
              FStar_Syntax_Embeddings.e_any in
          let uu___7 =
            FStar_Tactics_Interpreter.e_tactic_nbe_thunk
              FStar_TypeChecker_NBETerm.e_any in
          FStar_Tactics_InterpFuns.mk_tac_step_2 Prims.int_one "catch"
            FStar_Syntax_Embeddings.e_any uu___6
            (FStar_Syntax_Embeddings.e_either FStar_Tactics_Embedding.e_exn
               FStar_Syntax_Embeddings.e_any) FStar_TypeChecker_NBETerm.e_any
            uu___7
            (FStar_TypeChecker_NBETerm.e_either
               FStar_Tactics_Embedding.e_exn_nbe
               FStar_TypeChecker_NBETerm.e_any)
            (fun uu___8 -> FStar_Tactics_Monad.catch)
            (fun uu___8 -> FStar_Tactics_Monad.catch) in
        let uu___6 =
          let uu___7 =
            let uu___8 =
              FStar_Tactics_Interpreter.e_tactic_thunk
                FStar_Syntax_Embeddings.e_any in
            let uu___9 =
              FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                FStar_TypeChecker_NBETerm.e_any in
            FStar_Tactics_InterpFuns.mk_tac_step_2 Prims.int_one "recover"
              FStar_Syntax_Embeddings.e_any uu___8
              (FStar_Syntax_Embeddings.e_either FStar_Tactics_Embedding.e_exn
                 FStar_Syntax_Embeddings.e_any)
              FStar_TypeChecker_NBETerm.e_any uu___9
              (FStar_TypeChecker_NBETerm.e_either
                 FStar_Tactics_Embedding.e_exn_nbe
                 FStar_TypeChecker_NBETerm.e_any)
              (fun uu___10 -> FStar_Tactics_Monad.recover)
              (fun uu___10 -> FStar_Tactics_Monad.recover) in
          let uu___8 =
            let uu___9 =
              FStar_Tactics_InterpFuns.mk_tac_step_1 Prims.int_zero "intro"
                FStar_Syntax_Embeddings.e_unit
                FStar_Reflection_V2_Embeddings.e_binder
                FStar_TypeChecker_NBETerm.e_unit
                FStar_Reflection_V2_NBEEmbeddings.e_binder
                FStar_Tactics_V1_Basic.intro FStar_Tactics_V1_Basic.intro in
            let uu___10 =
              let uu___11 =
                FStar_Tactics_InterpFuns.mk_tac_step_1 Prims.int_zero
                  "intro_rec" FStar_Syntax_Embeddings.e_unit
                  (FStar_Syntax_Embeddings.e_tuple2
                     FStar_Reflection_V2_Embeddings.e_binder
                     FStar_Reflection_V2_Embeddings.e_binder)
                  FStar_TypeChecker_NBETerm.e_unit
                  (FStar_TypeChecker_NBETerm.e_tuple2
                     FStar_Reflection_V2_NBEEmbeddings.e_binder
                     FStar_Reflection_V2_NBEEmbeddings.e_binder)
                  FStar_Tactics_V1_Basic.intro_rec
                  FStar_Tactics_V1_Basic.intro_rec in
              let uu___12 =
                let uu___13 =
                  FStar_Tactics_InterpFuns.mk_tac_step_1 Prims.int_zero
                    "norm"
                    (FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_norm_step)
                    FStar_Syntax_Embeddings.e_unit
                    (FStar_TypeChecker_NBETerm.e_list
                       FStar_TypeChecker_NBETerm.e_norm_step)
                    FStar_TypeChecker_NBETerm.e_unit
                    FStar_Tactics_V1_Basic.norm FStar_Tactics_V1_Basic.norm in
                let uu___14 =
                  let uu___15 =
                    FStar_Tactics_InterpFuns.mk_tac_step_3 Prims.int_zero
                      "norm_term_env" FStar_Reflection_V2_Embeddings.e_env
                      (FStar_Syntax_Embeddings.e_list
                         FStar_Syntax_Embeddings.e_norm_step) uu___0 uu___0
                      FStar_Reflection_V2_NBEEmbeddings.e_env
                      (FStar_TypeChecker_NBETerm.e_list
                         FStar_TypeChecker_NBETerm.e_norm_step)
                      FStar_Reflection_V2_NBEEmbeddings.e_attribute
                      FStar_Reflection_V2_NBEEmbeddings.e_attribute
                      FStar_Tactics_V1_Basic.norm_term_env
                      FStar_Tactics_V1_Basic.norm_term_env in
                  let uu___16 =
                    let uu___17 =
                      FStar_Tactics_InterpFuns.mk_tac_step_2 Prims.int_zero
                        "norm_binder_type"
                        (FStar_Syntax_Embeddings.e_list
                           FStar_Syntax_Embeddings.e_norm_step)
                        FStar_Reflection_V2_Embeddings.e_binder
                        FStar_Syntax_Embeddings.e_unit
                        (FStar_TypeChecker_NBETerm.e_list
                           FStar_TypeChecker_NBETerm.e_norm_step)
                        FStar_Reflection_V2_NBEEmbeddings.e_binder
                        FStar_TypeChecker_NBETerm.e_unit
                        FStar_Tactics_V1_Basic.norm_binder_type
                        FStar_Tactics_V1_Basic.norm_binder_type in
                    let uu___18 =
                      let uu___19 =
                        FStar_Tactics_InterpFuns.mk_tac_step_2 Prims.int_zero
                          "rename_to" FStar_Reflection_V2_Embeddings.e_binder
                          FStar_Syntax_Embeddings.e_string
                          FStar_Reflection_V2_Embeddings.e_binder
                          FStar_Reflection_V2_NBEEmbeddings.e_binder
                          FStar_TypeChecker_NBETerm.e_string
                          FStar_Reflection_V2_NBEEmbeddings.e_binder
                          FStar_Tactics_V1_Basic.rename_to
                          FStar_Tactics_V1_Basic.rename_to in
                      let uu___20 =
                        let uu___21 =
                          FStar_Tactics_InterpFuns.mk_tac_step_1
                            Prims.int_zero "binder_retype"
                            FStar_Reflection_V2_Embeddings.e_binder
                            FStar_Syntax_Embeddings.e_unit
                            FStar_Reflection_V2_NBEEmbeddings.e_binder
                            FStar_TypeChecker_NBETerm.e_unit
                            FStar_Tactics_V1_Basic.binder_retype
                            FStar_Tactics_V1_Basic.binder_retype in
                        let uu___22 =
                          let uu___23 =
                            FStar_Tactics_InterpFuns.mk_tac_step_1
                              Prims.int_zero "revert"
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Syntax_Embeddings.e_unit
                              FStar_TypeChecker_NBETerm.e_unit
                              FStar_TypeChecker_NBETerm.e_unit
                              FStar_Tactics_V1_Basic.revert
                              FStar_Tactics_V1_Basic.revert in
                          let uu___24 =
                            let uu___25 =
                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                Prims.int_zero "clear_top"
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Syntax_Embeddings.e_unit
                                FStar_TypeChecker_NBETerm.e_unit
                                FStar_TypeChecker_NBETerm.e_unit
                                FStar_Tactics_V1_Basic.clear_top
                                FStar_Tactics_V1_Basic.clear_top in
                            let uu___26 =
                              let uu___27 =
                                FStar_Tactics_InterpFuns.mk_tac_step_1
                                  Prims.int_zero "clear"
                                  FStar_Reflection_V2_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Reflection_V2_NBEEmbeddings.e_binder
                                  FStar_TypeChecker_NBETerm.e_unit
                                  FStar_Tactics_V1_Basic.clear
                                  FStar_Tactics_V1_Basic.clear in
                              let uu___28 =
                                let uu___29 =
                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                    Prims.int_zero "rewrite"
                                    FStar_Reflection_V2_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Reflection_V2_NBEEmbeddings.e_binder
                                    FStar_TypeChecker_NBETerm.e_unit
                                    FStar_Tactics_V1_Basic.rewrite
                                    FStar_Tactics_V1_Basic.rewrite in
                                let uu___30 =
                                  let uu___31 =
                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                      Prims.int_zero "refine_intro"
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_TypeChecker_NBETerm.e_unit
                                      FStar_TypeChecker_NBETerm.e_unit
                                      FStar_Tactics_V1_Basic.refine_intro
                                      FStar_Tactics_V1_Basic.refine_intro in
                                  let uu___32 =
                                    let uu___33 =
                                      FStar_Tactics_InterpFuns.mk_tac_step_3
                                        Prims.int_zero "t_exact"
                                        FStar_Syntax_Embeddings.e_bool
                                        FStar_Syntax_Embeddings.e_bool uu___0
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_TypeChecker_NBETerm.e_bool
                                        FStar_TypeChecker_NBETerm.e_bool
                                        FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_Tactics_V1_Basic.t_exact
                                        FStar_Tactics_V1_Basic.t_exact in
                                    let uu___34 =
                                      let uu___35 =
                                        FStar_Tactics_InterpFuns.mk_tac_step_4
                                          Prims.int_zero "t_apply"
                                          FStar_Syntax_Embeddings.e_bool
                                          FStar_Syntax_Embeddings.e_bool
                                          FStar_Syntax_Embeddings.e_bool
                                          uu___0
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_TypeChecker_NBETerm.e_bool
                                          FStar_TypeChecker_NBETerm.e_bool
                                          FStar_TypeChecker_NBETerm.e_bool
                                          FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                          FStar_TypeChecker_NBETerm.e_unit
                                          FStar_Tactics_V1_Basic.t_apply
                                          FStar_Tactics_V1_Basic.t_apply in
                                      let uu___36 =
                                        let uu___37 =
                                          FStar_Tactics_InterpFuns.mk_tac_step_3
                                            Prims.int_zero "t_apply_lemma"
                                            FStar_Syntax_Embeddings.e_bool
                                            FStar_Syntax_Embeddings.e_bool
                                            uu___0
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_TypeChecker_NBETerm.e_bool
                                            FStar_TypeChecker_NBETerm.e_bool
                                            FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                            FStar_TypeChecker_NBETerm.e_unit
                                            FStar_Tactics_V1_Basic.t_apply_lemma
                                            FStar_Tactics_V1_Basic.t_apply_lemma in
                                        let uu___38 =
                                          let uu___39 =
                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                              Prims.int_zero "set_options"
                                              FStar_Syntax_Embeddings.e_string
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_TypeChecker_NBETerm.e_string
                                              FStar_TypeChecker_NBETerm.e_unit
                                              FStar_Tactics_V1_Basic.set_options
                                              FStar_Tactics_V1_Basic.set_options in
                                          let uu___40 =
                                            let uu___41 =
                                              FStar_Tactics_InterpFuns.mk_tac_step_2
                                                Prims.int_zero "tcc"
                                                FStar_Reflection_V2_Embeddings.e_env
                                                uu___0
                                                FStar_Reflection_V2_Embeddings.e_comp
                                                FStar_Reflection_V2_NBEEmbeddings.e_env
                                                FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                FStar_Reflection_V2_NBEEmbeddings.e_comp
                                                FStar_Tactics_V1_Basic.tcc
                                                FStar_Tactics_V1_Basic.tcc in
                                            let uu___42 =
                                              let uu___43 =
                                                FStar_Tactics_InterpFuns.mk_tac_step_2
                                                  Prims.int_zero "tc"
                                                  FStar_Reflection_V2_Embeddings.e_env
                                                  uu___0 uu___0
                                                  FStar_Reflection_V2_NBEEmbeddings.e_env
                                                  FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                  FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                  FStar_Tactics_V1_Basic.tc
                                                  FStar_Tactics_V1_Basic.tc in
                                              let uu___44 =
                                                let uu___45 =
                                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                                    Prims.int_zero "unshelve"
                                                    uu___0
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                    FStar_TypeChecker_NBETerm.e_unit
                                                    FStar_Tactics_V1_Basic.unshelve
                                                    FStar_Tactics_V1_Basic.unshelve in
                                                let uu___46 =
                                                  let uu___47 =
                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                      Prims.int_one "unquote"
                                                      FStar_Syntax_Embeddings.e_any
                                                      FStar_Reflection_V1_Embeddings.e_term
                                                      FStar_Syntax_Embeddings.e_any
                                                      FStar_TypeChecker_NBETerm.e_any
                                                      FStar_Reflection_V1_NBEEmbeddings.e_term
                                                      FStar_TypeChecker_NBETerm.e_any
                                                      FStar_Tactics_V1_Basic.unquote
                                                      (fun uu___48 ->
                                                         fun uu___49 ->
                                                           FStar_Compiler_Effect.failwith
                                                             "NBE unquote") in
                                                  let uu___48 =
                                                    let uu___49 =
                                                      FStar_Tactics_InterpFuns.mk_tac_step_1
                                                        Prims.int_zero
                                                        "prune"
                                                        FStar_Syntax_Embeddings.e_string
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_TypeChecker_NBETerm.e_string
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                        FStar_Tactics_V1_Basic.prune
                                                        FStar_Tactics_V1_Basic.prune in
                                                    let uu___50 =
                                                      let uu___51 =
                                                        FStar_Tactics_InterpFuns.mk_tac_step_1
                                                          Prims.int_zero
                                                          "addns"
                                                          FStar_Syntax_Embeddings.e_string
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_TypeChecker_NBETerm.e_string
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                          FStar_Tactics_V1_Basic.addns
                                                          FStar_Tactics_V1_Basic.addns in
                                                      let uu___52 =
                                                        let uu___53 =
                                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                                            Prims.int_zero
                                                            "print"
                                                            FStar_Syntax_Embeddings.e_string
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_TypeChecker_NBETerm.e_string
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_Tactics_V1_Basic.print
                                                            FStar_Tactics_V1_Basic.print in
                                                        let uu___54 =
                                                          let uu___55 =
                                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                                              Prims.int_zero
                                                              "debugging"
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Syntax_Embeddings.e_bool
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                              FStar_TypeChecker_NBETerm.e_bool
                                                              FStar_Tactics_V1_Basic.debugging
                                                              FStar_Tactics_V1_Basic.debugging in
                                                          let uu___56 =
                                                            let uu___57 =
                                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                Prims.int_zero
                                                                "dump"
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_TypeChecker_NBETerm.e_string
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                                FStar_Tactics_V1_Basic.dump
                                                                FStar_Tactics_V1_Basic.dump in
                                                            let uu___58 =
                                                              let uu___59 =
                                                                FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                  Prims.int_zero
                                                                  "dump_all"
                                                                  FStar_Syntax_Embeddings.e_bool
                                                                  FStar_Syntax_Embeddings.e_string
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_TypeChecker_NBETerm.e_bool
                                                                  FStar_TypeChecker_NBETerm.e_string
                                                                  FStar_TypeChecker_NBETerm.e_unit
                                                                  FStar_Tactics_V1_Basic.dump_all
                                                                  FStar_Tactics_V1_Basic.dump_all in
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "dump_uvars_of"
                                                                    FStar_Tactics_Embedding.e_goal
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_goal_nbe
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.dump_uvars_of
                                                                    FStar_Tactics_V1_Basic.dump_uvars_of in
                                                                let uu___62 =
                                                                  let uu___63
                                                                    =
                                                                    let uu___64
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_1
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag) in
                                                                    let uu___65
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu___66
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_nbe_1
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe) in
                                                                    let uu___67
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu___64
                                                                    uu___65
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu___66
                                                                    uu___67
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite in
                                                                  let uu___64
                                                                    =
                                                                    let uu___65
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_trefl"
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.t_trefl
                                                                    FStar_Tactics_V1_Basic.t_trefl in
                                                                    let uu___66
                                                                    =
                                                                    let uu___67
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dup"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.dup
                                                                    FStar_Tactics_V1_Basic.dup in
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "tadmit_t"
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.tadmit_t
                                                                    FStar_Tactics_V1_Basic.tadmit_t in
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "join"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.join
                                                                    FStar_Tactics_V1_Basic.join in
                                                                    let uu___72
                                                                    =
                                                                    let uu___73
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V2_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int))
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int))
                                                                    FStar_Tactics_V1_Basic.t_destruct
                                                                    FStar_Tactics_V1_Basic.t_destruct in
                                                                    let uu___74
                                                                    =
                                                                    let uu___75
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "top_env"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Tactics_V1_Basic.top_env
                                                                    FStar_Tactics_V1_Basic.top_env in
                                                                    let uu___76
                                                                    =
                                                                    let uu___77
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "inspect"
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V1_Embeddings.e_term_view
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term_view
                                                                    FStar_Tactics_V1_Basic.inspect
                                                                    FStar_Tactics_V1_Basic.inspect in
                                                                    let uu___78
                                                                    =
                                                                    let uu___79
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "pack"
                                                                    FStar_Reflection_V1_Embeddings.e_term_view
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term_view
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Tactics_V1_Basic.pack
                                                                    FStar_Tactics_V1_Basic.pack in
                                                                    let uu___80
                                                                    =
                                                                    let uu___81
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "pack_curried"
                                                                    FStar_Reflection_V1_Embeddings.e_term_view
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term_view
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Tactics_V1_Basic.pack_curried
                                                                    FStar_Tactics_V1_Basic.pack_curried in
                                                                    let uu___82
                                                                    =
                                                                    let uu___83
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Tactics_V1_Basic.fresh
                                                                    FStar_Tactics_V1_Basic.fresh in
                                                                    let uu___84
                                                                    =
                                                                    let uu___85
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "curms"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Tactics_V1_Basic.curms
                                                                    FStar_Tactics_V1_Basic.curms in
                                                                    let uu___86
                                                                    =
                                                                    let uu___87
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    (FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_V1_Embeddings.e_term)
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    (FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term)
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Tactics_V1_Basic.uvar_env
                                                                    FStar_Tactics_V1_Basic.uvar_env in
                                                                    let uu___88
                                                                    =
                                                                    let uu___89
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "ghost_uvar_env"
                                                                    FStar_Reflection_V2_Embeddings.e_env
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Tactics_V1_Basic.ghost_uvar_env
                                                                    FStar_Tactics_V1_Basic.ghost_uvar_env in
                                                                    let uu___90
                                                                    =
                                                                    let uu___91
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh_universe_uvar"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Tactics_V1_Basic.fresh_universe_uvar
                                                                    FStar_Tactics_V1_Basic.fresh_universe_uvar in
                                                                    let uu___92
                                                                    =
                                                                    let uu___93
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "unify_env"
                                                                    FStar_Reflection_V1_Embeddings.e_env
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V1_Basic.unify_env
                                                                    FStar_Tactics_V1_Basic.unify_env in
                                                                    let uu___94
                                                                    =
                                                                    let uu___95
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "unify_guard_env"
                                                                    FStar_Reflection_V1_Embeddings.e_env
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V1_Basic.unify_guard_env
                                                                    FStar_Tactics_V1_Basic.unify_guard_env in
                                                                    let uu___96
                                                                    =
                                                                    let uu___97
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "match_env"
                                                                    FStar_Reflection_V1_Embeddings.e_env
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V1_Basic.match_env
                                                                    FStar_Tactics_V1_Basic.match_env in
                                                                    let uu___98
                                                                    =
                                                                    let uu___99
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
                                                                    FStar_Tactics_V1_Basic.launch_process
                                                                    FStar_Tactics_V1_Basic.launch_process in
                                                                    let uu___100
                                                                    =
                                                                    let uu___101
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh_bv_named"
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_V1_Embeddings.e_bv
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_bv
                                                                    FStar_Tactics_V1_Basic.fresh_bv_named
                                                                    FStar_Tactics_V1_Basic.fresh_bv_named in
                                                                    let uu___102
                                                                    =
                                                                    let uu___103
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "change"
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.change
                                                                    FStar_Tactics_V1_Basic.change in
                                                                    let uu___104
                                                                    =
                                                                    let uu___105
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "get_guard_policy"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_Tactics_V1_Basic.get_guard_policy
                                                                    FStar_Tactics_V1_Basic.get_guard_policy in
                                                                    let uu___106
                                                                    =
                                                                    let uu___107
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.set_guard_policy
                                                                    FStar_Tactics_V1_Basic.set_guard_policy in
                                                                    let uu___108
                                                                    =
                                                                    let uu___109
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "lax_on"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V1_Basic.lax_on
                                                                    FStar_Tactics_V1_Basic.lax_on in
                                                                    let uu___110
                                                                    =
                                                                    let uu___111
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
                                                                    FStar_Tactics_V1_Basic.lget
                                                                    (fun
                                                                    uu___112
                                                                    ->
                                                                    fun
                                                                    uu___113
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE") in
                                                                    let uu___112
                                                                    =
                                                                    let uu___113
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
                                                                    FStar_Tactics_V1_Basic.lset
                                                                    (fun
                                                                    uu___114
                                                                    ->
                                                                    fun
                                                                    uu___115
                                                                    ->
                                                                    fun
                                                                    uu___116
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE") in
                                                                    let uu___114
                                                                    =
                                                                    let uu___115
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_urgency"
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.set_urgency
                                                                    FStar_Tactics_V1_Basic.set_urgency in
                                                                    let uu___116
                                                                    =
                                                                    let uu___117
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_commute_applied_match"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.t_commute_applied_match
                                                                    FStar_Tactics_V1_Basic.t_commute_applied_match in
                                                                    let uu___118
                                                                    =
                                                                    let uu___119
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "gather_or_solve_explicit_guards_for_resolved_goals"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.gather_explicit_guards_for_resolved_goals
                                                                    FStar_Tactics_V1_Basic.gather_explicit_guards_for_resolved_goals in
                                                                    let uu___120
                                                                    =
                                                                    let uu___121
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "string_to_term"
                                                                    FStar_Reflection_V1_Embeddings.e_env
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Tactics_V1_Basic.string_to_term
                                                                    FStar_Tactics_V1_Basic.string_to_term in
                                                                    let uu___122
                                                                    =
                                                                    let uu___123
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "push_bv_dsenv"
                                                                    FStar_Reflection_V1_Embeddings.e_env
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_V1_Embeddings.e_env
                                                                    FStar_Reflection_V1_Embeddings.e_bv)
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_env
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_env
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_bv)
                                                                    FStar_Tactics_V1_Basic.push_bv_dsenv
                                                                    FStar_Tactics_V1_Basic.push_bv_dsenv in
                                                                    let uu___124
                                                                    =
                                                                    let uu___125
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "term_to_string"
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Tactics_V1_Basic.term_to_string
                                                                    FStar_Tactics_V1_Basic.term_to_string in
                                                                    let uu___126
                                                                    =
                                                                    let uu___127
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "comp_to_string"
                                                                    FStar_Reflection_V2_Embeddings.e_comp
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_V2_NBEEmbeddings.e_comp
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Tactics_V1_Basic.comp_to_string
                                                                    FStar_Tactics_V1_Basic.comp_to_string in
                                                                    let uu___128
                                                                    =
                                                                    let uu___129
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "range_to_string"
                                                                    FStar_Syntax_Embeddings.e_range
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_TypeChecker_NBETerm.e_range
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Tactics_V1_Basic.range_to_string
                                                                    FStar_Tactics_V1_Basic.range_to_string in
                                                                    let uu___130
                                                                    =
                                                                    let uu___131
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "term_eq_old"
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_V1_Basic.term_eq_old
                                                                    FStar_Tactics_V1_Basic.term_eq_old in
                                                                    let uu___132
                                                                    =
                                                                    let uu___133
                                                                    =
                                                                    let uu___134
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_any in
                                                                    let uu___135
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "with_compat_pre_core"
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    uu___134
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    uu___135
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    (fun
                                                                    uu___136
                                                                    ->
                                                                    FStar_Tactics_V1_Basic.with_compat_pre_core)
                                                                    (fun
                                                                    uu___136
                                                                    ->
                                                                    FStar_Tactics_V1_Basic.with_compat_pre_core) in
                                                                    let uu___134
                                                                    =
                                                                    let uu___135
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "get_vconfig"
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_vconfig
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_vconfig
                                                                    FStar_Tactics_V1_Basic.get_vconfig
                                                                    FStar_Tactics_V1_Basic.get_vconfig in
                                                                    let uu___136
                                                                    =
                                                                    let uu___137
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_vconfig"
                                                                    FStar_Syntax_Embeddings.e_vconfig
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_vconfig
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.set_vconfig
                                                                    FStar_Tactics_V1_Basic.set_vconfig in
                                                                    let uu___138
                                                                    =
                                                                    let uu___139
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_smt_sync"
                                                                    FStar_Syntax_Embeddings.e_vconfig
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_vconfig
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_V1_Basic.t_smt_sync
                                                                    FStar_Tactics_V1_Basic.t_smt_sync in
                                                                    let uu___140
                                                                    =
                                                                    let uu___141
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "free_uvars"
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_int)
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_int)
                                                                    FStar_Tactics_V1_Basic.free_uvars
                                                                    FStar_Tactics_V1_Basic.free_uvars in
                                                                    [uu___141] in
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
    uu___1 :: uu___2 in
  FStar_Compiler_List.map fix_module uu___