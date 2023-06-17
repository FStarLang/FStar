open Prims
let rec (combine_if_branches :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Typing_Env.env ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Syntax_Base.comp_st ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  ((Pulse_Syntax_Base.comp_st,
                     (unit, unit, unit) Pulse_Typing.st_typing,
                     (unit, unit, unit) Pulse_Typing.st_typing)
                     FStar_Pervasives.dtuple3,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g_then ->
    fun e_then ->
      fun c_then ->
        fun e_then_typing ->
          fun g_else ->
            fun e_else ->
              fun c_else ->
                fun e_else_typing ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.If.fst"
                       (Prims.of_int (30)) (Prims.of_int (10))
                       (Prims.of_int (30)) (Prims.of_int (16)))
                    (FStar_Range.mk_range "Pulse.Checker.If.fst"
                       (Prims.of_int (31)) (Prims.of_int (2))
                       (Prims.of_int (72)) (Prims.of_int (78)))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> g_then))
                    (fun uu___ ->
                       (fun g ->
                          if
                            Pulse_Syntax_Base.eq_st_comp
                              (Pulse_Syntax_Base.st_comp_of_comp c_then)
                              (Pulse_Syntax_Base.st_comp_of_comp c_else)
                          then
                            Obj.magic
                              (Obj.repr
                                 (match (c_then, c_else) with
                                  | (Pulse_Syntax_Base.C_ST uu___,
                                     Pulse_Syntax_Base.C_ST uu___1) ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              FStar_Pervasives.Mkdtuple3
                                                (c_then, e_then_typing,
                                                  e_else_typing)))
                                  | (Pulse_Syntax_Base.C_STAtomic
                                     (inames1, uu___),
                                     Pulse_Syntax_Base.C_STAtomic
                                     (inames2, uu___1)) ->
                                      Obj.repr
                                        (if
                                           Pulse_Syntax_Base.eq_tm inames1
                                             inames2
                                         then
                                           Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pervasives.Mkdtuple3
                                                     (c_then, e_then_typing,
                                                       e_else_typing)))
                                         else
                                           Obj.repr
                                             (Pulse_Typing_Env.fail g
                                                FStar_Pervasives_Native.None
                                                "Cannot combine then and else branches (different inames)"))
                                  | (Pulse_Syntax_Base.C_STGhost
                                     (inames1, uu___),
                                     Pulse_Syntax_Base.C_STGhost
                                     (inames2, uu___1)) ->
                                      Obj.repr
                                        (if
                                           Pulse_Syntax_Base.eq_tm inames1
                                             inames2
                                         then
                                           Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pervasives.Mkdtuple3
                                                     (c_then, e_then_typing,
                                                       e_else_typing)))
                                         else
                                           Obj.repr
                                             (Pulse_Typing_Env.fail g
                                                FStar_Pervasives_Native.None
                                                "Cannot combine then and else branches (different inames)"))
                                  | (Pulse_Syntax_Base.C_ST uu___,
                                     Pulse_Syntax_Base.C_STAtomic
                                     (inames, uu___1)) ->
                                      Obj.repr
                                        (if
                                           Pulse_Syntax_Base.eq_tm inames
                                             Pulse_Syntax_Base.Tm_EmpInames
                                         then
                                           Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pervasives.Mkdtuple3
                                                     (c_then, e_then_typing,
                                                       (Pulse_Typing.T_Lift
                                                          (g_else, e_else,
                                                            c_else, c_then,
                                                            e_else_typing,
                                                            (Pulse_Typing.Lift_STAtomic_ST
                                                               (g_else,
                                                                 c_else)))))))
                                         else
                                           Obj.repr
                                             (Pulse_Typing_Env.fail g
                                                FStar_Pervasives_Native.None
                                                "Cannot lift STAtomic else branch to match then"))
                                  | (Pulse_Syntax_Base.C_STAtomic
                                     (inames, uu___), Pulse_Syntax_Base.C_ST
                                     uu___1) ->
                                      Obj.repr
                                        (if
                                           Pulse_Syntax_Base.eq_tm inames
                                             Pulse_Syntax_Base.Tm_EmpInames
                                         then
                                           Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pervasives.Mkdtuple3
                                                     (c_else,
                                                       (Pulse_Typing.T_Lift
                                                          (g_then, e_then,
                                                            c_then, c_else,
                                                            e_then_typing,
                                                            (Pulse_Typing.Lift_STAtomic_ST
                                                               (g_then,
                                                                 c_then)))),
                                                       e_else_typing)))
                                         else
                                           Obj.repr
                                             (Pulse_Typing_Env.fail g
                                                FStar_Pervasives_Native.None
                                                "Cannot lift STAtomic else branch to match then"))
                                  | (Pulse_Syntax_Base.C_STGhost
                                     (uu___, uu___1), uu___2) ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.If.fst"
                                              (Prims.of_int (59))
                                              (Prims.of_int (14))
                                              (Prims.of_int (59))
                                              (Prims.of_int (82)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.If.fst"
                                              (Prims.of_int (59))
                                              (Prims.of_int (85))
                                              (Prims.of_int (64))
                                              (Prims.of_int (35)))
                                           (Obj.magic
                                              (Pulse_Checker_Pure.get_non_informative_witness
                                                 g_then
                                                 (Pulse_Syntax_Base.comp_u
                                                    c_then)
                                                 (Pulse_Syntax_Base.comp_res
                                                    c_then)))
                                           (fun uu___3 ->
                                              (fun w ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (61))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (61))
                                                         (Prims.of_int (66)))
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (61))
                                                         (Prims.of_int (69))
                                                         (Prims.of_int (64))
                                                         (Prims.of_int (35)))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            Pulse_Typing.T_Lift
                                                              (g_then,
                                                                e_then,
                                                                c_then,
                                                                (Pulse_Syntax_Base.C_STAtomic
                                                                   ((Pulse_Syntax_Base.comp_inames
                                                                    c_then),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_then))),
                                                                e_then_typing,
                                                                (Pulse_Typing.Lift_STGhost_STAtomic
                                                                   (g_then,
                                                                    c_then,
                                                                    w)))))
                                                      (fun uu___3 ->
                                                         (fun e_then_typing1
                                                            ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (67)))
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (35)))
                                                                 (Obj.magic
                                                                    (
                                                                    combine_if_branches
                                                                    g_then
                                                                    e_then
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c_then),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_then)))
                                                                    e_then_typing1
                                                                    g_else
                                                                    e_else
                                                                    c_else
                                                                    e_else_typing))
                                                                 (fun uu___3
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c,
                                                                    e1_typing,
                                                                    e2_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c,
                                                                    e1_typing,
                                                                    e2_typing)))))
                                                           uu___3))) uu___3))
                                  | (uu___, Pulse_Syntax_Base.C_STGhost
                                     (uu___1, uu___2)) ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.If.fst"
                                              (Prims.of_int (66))
                                              (Prims.of_int (14))
                                              (Prims.of_int (66))
                                              (Prims.of_int (82)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.If.fst"
                                              (Prims.of_int (66))
                                              (Prims.of_int (85))
                                              (Prims.of_int (69))
                                              (Prims.of_int (65)))
                                           (Obj.magic
                                              (Pulse_Checker_Pure.get_non_informative_witness
                                                 g_else
                                                 (Pulse_Syntax_Base.comp_u
                                                    c_else)
                                                 (Pulse_Syntax_Base.comp_res
                                                    c_else)))
                                           (fun uu___3 ->
                                              (fun w ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (68))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (68))
                                                         (Prims.of_int (66)))
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (69))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (69))
                                                         (Prims.of_int (65)))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            Pulse_Typing.T_Lift
                                                              (g_else,
                                                                e_else,
                                                                c_else,
                                                                (Pulse_Syntax_Base.C_STAtomic
                                                                   ((Pulse_Syntax_Base.comp_inames
                                                                    c_else),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_else))),
                                                                e_else_typing,
                                                                (Pulse_Typing.Lift_STGhost_STAtomic
                                                                   (g_else,
                                                                    c_else,
                                                                    w)))))
                                                      (fun uu___3 ->
                                                         (fun e_else_typing1
                                                            ->
                                                            Obj.magic
                                                              (combine_if_branches
                                                                 g_then
                                                                 e_then
                                                                 c_then
                                                                 e_then_typing
                                                                 g_else
                                                                 e_else
                                                                 (Pulse_Syntax_Base.C_STAtomic
                                                                    ((Pulse_Syntax_Base.comp_inames
                                                                    c_else),
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_else)))
                                                                 e_else_typing1))
                                                           uu___3))) uu___3))
                                  | (uu___, uu___1) ->
                                      Obj.repr
                                        (Pulse_Typing_Env.fail g
                                           FStar_Pervasives_Native.None
                                           "Cannot combine then and else branches (incompatible effects)")))
                          else
                            Obj.magic
                              (Obj.repr
                                 (Pulse_Typing_Env.fail g
                                    FStar_Pervasives_Native.None
                                    "Cannot combine then and else branches (different st_comp)")))
                         uu___)
let (check_if :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.term ->
            unit ->
              unit Pulse_Checker_Common.post_hint_for_env ->
                Pulse_Checker_Common.check_t ->
                  ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      fun e1 ->
        fun e2 ->
          fun pre ->
            fun pre_typing ->
              fun post_hint ->
                fun check ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.If.fst"
                       (Prims.of_int (85)) (Prims.of_int (6))
                       (Prims.of_int (85)) (Prims.of_int (47)))
                    (FStar_Range.mk_range "Pulse.Checker.If.fst"
                       (Prims.of_int (84)) (Prims.of_int (3))
                       (Prims.of_int (131)) (Prims.of_int (78)))
                    (Obj.magic
                       (Pulse_Checker_Pure.check_term_with_expected_type g b
                          Pulse_Typing.tm_bool))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | Prims.Mkdtuple2 (b1, b_typing) ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.If.fst"
                                      (Prims.of_int (86)) (Prims.of_int (15))
                                      (Prims.of_int (86)) (Prims.of_int (29)))
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.If.fst"
                                      (Prims.of_int (86)) (Prims.of_int (32))
                                      (Prims.of_int (131))
                                      (Prims.of_int (78)))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 ->
                                         post_hint.Pulse_Checker_Common.post))
                                   (fun uu___1 ->
                                      (fun post ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.If.fst"
                                                 (Prims.of_int (87))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (87))
                                                 (Prims.of_int (21)))
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.If.fst"
                                                 (Prims.of_int (87))
                                                 (Prims.of_int (24))
                                                 (Prims.of_int (131))
                                                 (Prims.of_int (78)))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Pulse_Typing_Env.fresh g))
                                              (fun uu___1 ->
                                                 (fun hyp ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.If.fst"
                                                            (Prims.of_int (89))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (89))
                                                            (Prims.of_int (53)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.If.fst"
                                                            (Prims.of_int (90))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (131))
                                                            (Prims.of_int (78)))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___1 ->
                                                               fun eq_v ->
                                                                 Pulse_Typing_Env.push_binding
                                                                   g hyp
                                                                   (Pulse_Typing.mk_eq2
                                                                    Pulse_Syntax_Pure.u0
                                                                    Pulse_Typing.tm_bool
                                                                    b1 eq_v)))
                                                         (fun uu___1 ->
                                                            (fun g_with_eq ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (35)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (78)))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    fun eq_v
                                                                    ->
                                                                    fun br ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    g_with_eq
                                                                    eq_v))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    g_with_eq1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (check
                                                                    g_with_eq1
                                                                    br pre ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c,
                                                                    br_typing)
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    hyp
                                                                    (Pulse_Syntax_Naming.freevars_st
                                                                    br1)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (br1.Pulse_Syntax_Base.range1))
                                                                    "Illegal use of control-flow hypothesis in branch"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c)
                                                                    then
                                                                    Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (br1.Pulse_Syntax_Base.range1))
                                                                    "Branch computation type not st")
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c,
                                                                    br_typing))))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    check_branch
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    Pulse_Typing.tm_true
                                                                    e1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e11, c1,
                                                                    e1_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    Pulse_Typing.tm_false
                                                                    e2))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e21, c2,
                                                                    e2_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (combine_if_branches
                                                                    (g_with_eq
                                                                    Pulse_Typing.tm_true)
                                                                    e11 c1
                                                                    e1_typing
                                                                    (g_with_eq
                                                                    Pulse_Typing.tm_false)
                                                                    e21 c2
                                                                    e2_typing))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (c,
                                                                    e1_typing1,
                                                                    e2_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (7)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (7)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post)
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Unexpected name clash")
                                                                    else
                                                                    if
                                                                    Prims.op_Negation
                                                                    (((Pulse_Syntax_Base.eq_tm
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c)
                                                                    post_hint.Pulse_Checker_Common.ret_ty)
                                                                    &&
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c)
                                                                    post_hint.Pulse_Checker_Common.u))
                                                                    &&
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)
                                                                    post_hint.Pulse_Checker_Common.post))
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Unexpected result type in branches")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (88)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Checker_Common.post_hint_typing
                                                                    g
                                                                    post_hint
                                                                    x))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    post_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.intro_comp_typing
                                                                    g c () ()
                                                                    x ()))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_If
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b1;
                                                                    Pulse_Syntax_Base.then_
                                                                    = e11;
                                                                    Pulse_Syntax_Base.else_
                                                                    = e21;
                                                                    Pulse_Syntax_Base.post2
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })), c,
                                                                    (Pulse_Typing.T_If
                                                                    (g, b1,
                                                                    e11, e21,
                                                                    c,
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c), hyp,
                                                                    (),
                                                                    e1_typing1,
                                                                    e2_typing1,
                                                                    ())))))))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                              uu___1)))
                                                   uu___1))) uu___1))) uu___)