open Prims
let solve : 'a . 'a -> 'a = fun ev -> ev
let (uu___2 :
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
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_Compiler_List.tl p in
                FStar_Compiler_List.tl uu___6 in
              FStar_Compiler_List.tl uu___5 in
            FStar_Compiler_List.tl uu___4 in
          FStar_Compiler_List.tl uu___3 in
        FStar_Compiler_List.op_At
          ["FStar"; "Stubs"; "Tactics"; "V1"; "Builtins"] uu___1 in
      let uu___1 =
        let uu___3 =
          FStar_Class_HasRange.pos FStar_Ident.hasrange_lident
            ps.FStar_TypeChecker_Primops_Base.name in
        FStar_Ident.lid_of_path p' uu___3 in
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
    let uu___3 =
      let uu___4 =
        FStar_Tactics_InterpFuns.mk_tac_step_1 Prims.int_zero "set_smt_goals"
          (FStar_Syntax_Embeddings.e_list FStar_Tactics_Embedding.e_goal)
          FStar_Syntax_Embeddings.e_unit
          (FStar_TypeChecker_NBETerm.e_list
             FStar_Tactics_Embedding.e_goal_nbe)
          FStar_TypeChecker_NBETerm.e_unit FStar_Tactics_Monad.set_smt_goals
          FStar_Tactics_Monad.set_smt_goals in
      let uu___5 =
        let uu___6 =
          let uu___7 =
            FStar_Tactics_Interpreter.e_tactic_thunk
              FStar_Syntax_Embeddings.e_any in
          let uu___8 =
            FStar_Tactics_Interpreter.e_tactic_nbe_thunk
              FStar_TypeChecker_NBETerm.e_any in
          FStar_Tactics_InterpFuns.mk_tac_step_2 Prims.int_one "catch"
            FStar_Syntax_Embeddings.e_any uu___7
            (FStar_Syntax_Embeddings.e_either FStar_Tactics_Embedding.e_exn
               FStar_Syntax_Embeddings.e_any) FStar_TypeChecker_NBETerm.e_any
            uu___8
            (FStar_TypeChecker_NBETerm.e_either
               FStar_Tactics_Embedding.e_exn_nbe
               FStar_TypeChecker_NBETerm.e_any)
            (fun uu___9 -> FStar_Tactics_Monad.catch)
            (fun uu___9 -> FStar_Tactics_Monad.catch) in
        let uu___7 =
          let uu___8 =
            let uu___9 =
              FStar_Tactics_Interpreter.e_tactic_thunk
                FStar_Syntax_Embeddings.e_any in
            let uu___10 =
              FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                FStar_TypeChecker_NBETerm.e_any in
            FStar_Tactics_InterpFuns.mk_tac_step_2 Prims.int_one "recover"
              FStar_Syntax_Embeddings.e_any uu___9
              (FStar_Syntax_Embeddings.e_either FStar_Tactics_Embedding.e_exn
                 FStar_Syntax_Embeddings.e_any)
              FStar_TypeChecker_NBETerm.e_any uu___10
              (FStar_TypeChecker_NBETerm.e_either
                 FStar_Tactics_Embedding.e_exn_nbe
                 FStar_TypeChecker_NBETerm.e_any)
              (fun uu___11 -> FStar_Tactics_Monad.recover)
              (fun uu___11 -> FStar_Tactics_Monad.recover) in
          let uu___9 =
            let uu___10 =
              FStar_Tactics_InterpFuns.mk_tac_step_1 Prims.int_zero "intro"
                FStar_Syntax_Embeddings.e_unit
                FStar_Reflection_V2_Embeddings.e_binder
                FStar_TypeChecker_NBETerm.e_unit
                FStar_Reflection_V2_NBEEmbeddings.e_binder
                FStar_Tactics_V1_Basic.intro FStar_Tactics_V1_Basic.intro in
            let uu___11 =
              let uu___12 =
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
              let uu___13 =
                let uu___14 =
                  FStar_Tactics_InterpFuns.mk_tac_step_1 Prims.int_zero
                    "norm"
                    (FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_norm_step)
                    FStar_Syntax_Embeddings.e_unit
                    (FStar_TypeChecker_NBETerm.e_list
                       FStar_TypeChecker_NBETerm.e_norm_step)
                    FStar_TypeChecker_NBETerm.e_unit
                    FStar_Tactics_V1_Basic.norm FStar_Tactics_V1_Basic.norm in
                let uu___15 =
                  let uu___16 =
                    FStar_Tactics_InterpFuns.mk_tac_step_3 Prims.int_zero
                      "norm_term_env" FStar_Reflection_V2_Embeddings.e_env
                      (FStar_Syntax_Embeddings.e_list
                         FStar_Syntax_Embeddings.e_norm_step) uu___2 uu___2
                      FStar_Reflection_V2_NBEEmbeddings.e_env
                      (FStar_TypeChecker_NBETerm.e_list
                         FStar_TypeChecker_NBETerm.e_norm_step)
                      FStar_Reflection_V2_NBEEmbeddings.e_attribute
                      FStar_Reflection_V2_NBEEmbeddings.e_attribute
                      FStar_Tactics_V1_Basic.norm_term_env
                      FStar_Tactics_V1_Basic.norm_term_env in
                  let uu___17 =
                    let uu___18 =
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
                    let uu___19 =
                      let uu___20 =
                        FStar_Tactics_InterpFuns.mk_tac_step_2 Prims.int_zero
                          "rename_to" FStar_Reflection_V2_Embeddings.e_binder
                          FStar_Syntax_Embeddings.e_string
                          FStar_Reflection_V2_Embeddings.e_binder
                          FStar_Reflection_V2_NBEEmbeddings.e_binder
                          FStar_TypeChecker_NBETerm.e_string
                          FStar_Reflection_V2_NBEEmbeddings.e_binder
                          FStar_Tactics_V1_Basic.rename_to
                          FStar_Tactics_V1_Basic.rename_to in
                      let uu___21 =
                        let uu___22 =
                          FStar_Tactics_InterpFuns.mk_tac_step_1
                            Prims.int_zero "binder_retype"
                            FStar_Reflection_V2_Embeddings.e_binder
                            FStar_Syntax_Embeddings.e_unit
                            FStar_Reflection_V2_NBEEmbeddings.e_binder
                            FStar_TypeChecker_NBETerm.e_unit
                            FStar_Tactics_V1_Basic.binder_retype
                            FStar_Tactics_V1_Basic.binder_retype in
                        let uu___23 =
                          let uu___24 =
                            FStar_Tactics_InterpFuns.mk_tac_step_1
                              Prims.int_zero "revert"
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Syntax_Embeddings.e_unit
                              FStar_TypeChecker_NBETerm.e_unit
                              FStar_TypeChecker_NBETerm.e_unit
                              FStar_Tactics_V1_Basic.revert
                              FStar_Tactics_V1_Basic.revert in
                          let uu___25 =
                            let uu___26 =
                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                Prims.int_zero "clear_top"
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Syntax_Embeddings.e_unit
                                FStar_TypeChecker_NBETerm.e_unit
                                FStar_TypeChecker_NBETerm.e_unit
                                FStar_Tactics_V1_Basic.clear_top
                                FStar_Tactics_V1_Basic.clear_top in
                            let uu___27 =
                              let uu___28 =
                                FStar_Tactics_InterpFuns.mk_tac_step_1
                                  Prims.int_zero "clear"
                                  FStar_Reflection_V2_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Reflection_V2_NBEEmbeddings.e_binder
                                  FStar_TypeChecker_NBETerm.e_unit
                                  FStar_Tactics_V1_Basic.clear
                                  FStar_Tactics_V1_Basic.clear in
                              let uu___29 =
                                let uu___30 =
                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                    Prims.int_zero "rewrite"
                                    FStar_Reflection_V2_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Reflection_V2_NBEEmbeddings.e_binder
                                    FStar_TypeChecker_NBETerm.e_unit
                                    FStar_Tactics_V1_Basic.rewrite
                                    FStar_Tactics_V1_Basic.rewrite in
                                let uu___31 =
                                  let uu___32 =
                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                      Prims.int_zero "refine_intro"
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_TypeChecker_NBETerm.e_unit
                                      FStar_TypeChecker_NBETerm.e_unit
                                      FStar_Tactics_V1_Basic.refine_intro
                                      FStar_Tactics_V1_Basic.refine_intro in
                                  let uu___33 =
                                    let uu___34 =
                                      FStar_Tactics_InterpFuns.mk_tac_step_3
                                        Prims.int_zero "t_exact"
                                        FStar_Syntax_Embeddings.e_bool
                                        FStar_Syntax_Embeddings.e_bool uu___2
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_TypeChecker_NBETerm.e_bool
                                        FStar_TypeChecker_NBETerm.e_bool
                                        FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_Tactics_V1_Basic.t_exact
                                        FStar_Tactics_V1_Basic.t_exact in
                                    let uu___35 =
                                      let uu___36 =
                                        FStar_Tactics_InterpFuns.mk_tac_step_4
                                          Prims.int_zero "t_apply"
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
                                          FStar_Tactics_V1_Basic.t_apply
                                          FStar_Tactics_V1_Basic.t_apply in
                                      let uu___37 =
                                        let uu___38 =
                                          FStar_Tactics_InterpFuns.mk_tac_step_3
                                            Prims.int_zero "t_apply_lemma"
                                            FStar_Syntax_Embeddings.e_bool
                                            FStar_Syntax_Embeddings.e_bool
                                            uu___2
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_TypeChecker_NBETerm.e_bool
                                            FStar_TypeChecker_NBETerm.e_bool
                                            FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                            FStar_TypeChecker_NBETerm.e_unit
                                            FStar_Tactics_V1_Basic.t_apply_lemma
                                            FStar_Tactics_V1_Basic.t_apply_lemma in
                                        let uu___39 =
                                          let uu___40 =
                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                              Prims.int_zero "set_options"
                                              FStar_Syntax_Embeddings.e_string
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_TypeChecker_NBETerm.e_string
                                              FStar_TypeChecker_NBETerm.e_unit
                                              FStar_Tactics_V1_Basic.set_options
                                              FStar_Tactics_V1_Basic.set_options in
                                          let uu___41 =
                                            let uu___42 =
                                              FStar_Tactics_InterpFuns.mk_tac_step_2
                                                Prims.int_zero "tcc"
                                                FStar_Reflection_V2_Embeddings.e_env
                                                uu___2
                                                FStar_Reflection_V2_Embeddings.e_comp
                                                FStar_Reflection_V2_NBEEmbeddings.e_env
                                                FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                FStar_Reflection_V2_NBEEmbeddings.e_comp
                                                FStar_Tactics_V1_Basic.tcc
                                                FStar_Tactics_V1_Basic.tcc in
                                            let uu___43 =
                                              let uu___44 =
                                                FStar_Tactics_InterpFuns.mk_tac_step_2
                                                  Prims.int_zero "tc"
                                                  FStar_Reflection_V2_Embeddings.e_env
                                                  uu___2 uu___2
                                                  FStar_Reflection_V2_NBEEmbeddings.e_env
                                                  FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                  FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                  FStar_Tactics_V1_Basic.tc
                                                  FStar_Tactics_V1_Basic.tc in
                                              let uu___45 =
                                                let uu___46 =
                                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                                    Prims.int_zero "unshelve"
                                                    uu___2
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Reflection_V2_NBEEmbeddings.e_attribute
                                                    FStar_TypeChecker_NBETerm.e_unit
                                                    FStar_Tactics_V1_Basic.unshelve
                                                    FStar_Tactics_V1_Basic.unshelve in
                                                let uu___47 =
                                                  let uu___48 =
                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                      Prims.int_one "unquote"
                                                      FStar_Syntax_Embeddings.e_any
                                                      FStar_Reflection_V1_Embeddings.e_term
                                                      FStar_Syntax_Embeddings.e_any
                                                      FStar_TypeChecker_NBETerm.e_any
                                                      FStar_Reflection_V1_NBEEmbeddings.e_term
                                                      FStar_TypeChecker_NBETerm.e_any
                                                      FStar_Tactics_V1_Basic.unquote
                                                      (fun uu___49 ->
                                                         fun uu___50 ->
                                                           FStar_Compiler_Effect.failwith
                                                             "NBE unquote") in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      FStar_Tactics_InterpFuns.mk_tac_step_1
                                                        Prims.int_zero
                                                        "prune"
                                                        FStar_Syntax_Embeddings.e_string
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_TypeChecker_NBETerm.e_string
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                        FStar_Tactics_V1_Basic.prune
                                                        FStar_Tactics_V1_Basic.prune in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        FStar_Tactics_InterpFuns.mk_tac_step_1
                                                          Prims.int_zero
                                                          "addns"
                                                          FStar_Syntax_Embeddings.e_string
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_TypeChecker_NBETerm.e_string
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                          FStar_Tactics_V1_Basic.addns
                                                          FStar_Tactics_V1_Basic.addns in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                                            Prims.int_zero
                                                            "print"
                                                            FStar_Syntax_Embeddings.e_string
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_TypeChecker_NBETerm.e_string
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_Tactics_V1_Basic.print
                                                            FStar_Tactics_V1_Basic.print in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                                              Prims.int_zero
                                                              "debugging"
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Syntax_Embeddings.e_bool
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                              FStar_TypeChecker_NBETerm.e_bool
                                                              FStar_Tactics_V1_Basic.debugging
                                                              FStar_Tactics_V1_Basic.debugging in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                Prims.int_zero
                                                                "dump"
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_TypeChecker_NBETerm.e_string
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                                FStar_Tactics_V1_Basic.dump
                                                                FStar_Tactics_V1_Basic.dump in
                                                            let uu___59 =
                                                              let uu___60 =
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
                                                              let uu___61 =
                                                                let uu___62 =
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
                                                                let uu___63 =
                                                                  let uu___64
                                                                    =
                                                                    let uu___65
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_1
                                                                    FStar_Reflection_V1_Embeddings.e_term
                                                                    (FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag) in
                                                                    let uu___66
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu___67
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_nbe_1
                                                                    FStar_Reflection_V1_NBEEmbeddings.e_term
                                                                    (FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe) in
                                                                    let uu___68
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu___65
                                                                    uu___66
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu___67
                                                                    uu___68
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite in
                                                                  let uu___65
                                                                    =
                                                                    let uu___66
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
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
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
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
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
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
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
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
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
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
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
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
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
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
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
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
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
                                                                    let uu___83
                                                                    =
                                                                    let uu___84
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
                                                                    let uu___85
                                                                    =
                                                                    let uu___86
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
                                                                    let uu___87
                                                                    =
                                                                    let uu___88
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
                                                                    let uu___89
                                                                    =
                                                                    let uu___90
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
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
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
                                                                    let uu___93
                                                                    =
                                                                    let uu___94
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
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
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
                                                                    let uu___97
                                                                    =
                                                                    let uu___98
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
                                                                    let uu___99
                                                                    =
                                                                    let uu___100
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
                                                                    let uu___101
                                                                    =
                                                                    let uu___102
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
                                                                    let uu___103
                                                                    =
                                                                    let uu___104
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
                                                                    let uu___105
                                                                    =
                                                                    let uu___106
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
                                                                    let uu___107
                                                                    =
                                                                    let uu___108
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
                                                                    let uu___109
                                                                    =
                                                                    let uu___110
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
                                                                    let uu___111
                                                                    =
                                                                    let uu___112
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
                                                                    uu___113
                                                                    ->
                                                                    fun
                                                                    uu___114
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE") in
                                                                    let uu___113
                                                                    =
                                                                    let uu___114
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
                                                                    uu___115
                                                                    ->
                                                                    fun
                                                                    uu___116
                                                                    ->
                                                                    fun
                                                                    uu___117
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE") in
                                                                    let uu___115
                                                                    =
                                                                    let uu___116
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
                                                                    let uu___117
                                                                    =
                                                                    let uu___118
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
                                                                    let uu___119
                                                                    =
                                                                    let uu___120
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
                                                                    let uu___121
                                                                    =
                                                                    let uu___122
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
                                                                    let uu___123
                                                                    =
                                                                    let uu___124
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
                                                                    let uu___125
                                                                    =
                                                                    let uu___126
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
                                                                    let uu___127
                                                                    =
                                                                    let uu___128
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
                                                                    let uu___129
                                                                    =
                                                                    let uu___130
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
                                                                    let uu___131
                                                                    =
                                                                    let uu___132
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
                                                                    let uu___133
                                                                    =
                                                                    let uu___134
                                                                    =
                                                                    let uu___135
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_any in
                                                                    let uu___136
                                                                    =
                                                                    FStar_Tactics_Interpreter.e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "with_compat_pre_core"
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    uu___135
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    uu___136
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    (fun
                                                                    uu___137
                                                                    ->
                                                                    FStar_Tactics_V1_Basic.with_compat_pre_core)
                                                                    (fun
                                                                    uu___137
                                                                    ->
                                                                    FStar_Tactics_V1_Basic.with_compat_pre_core) in
                                                                    let uu___135
                                                                    =
                                                                    let uu___136
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
                                                                    let uu___137
                                                                    =
                                                                    let uu___138
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
                                                                    let uu___139
                                                                    =
                                                                    let uu___140
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
                                                                    let uu___141
                                                                    =
                                                                    let uu___142
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
                                                                    [uu___142] in
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
    uu___1 :: uu___3 in
  FStar_Compiler_List.map fix_module uu___