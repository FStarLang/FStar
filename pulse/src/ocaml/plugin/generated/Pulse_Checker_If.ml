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
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.If.fst"
                             (Prims.of_int (30)) (Prims.of_int (10))
                             (Prims.of_int (30)) (Prims.of_int (16)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.If.fst"
                             (Prims.of_int (31)) (Prims.of_int (2))
                             (Prims.of_int (83)) (Prims.of_int (78)))))
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
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (40))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (42))
                                                         (Prims.of_int (43)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (39))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (42))
                                                         (Prims.of_int (43)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.If.fst"
                                                               (Prims.of_int (42))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (42))
                                                               (Prims.of_int (42)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.If.fst"
                                                               (Prims.of_int (40))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (42))
                                                               (Prims.of_int (43)))))
                                                      (Obj.magic
                                                         (Pulse_Syntax_Printer.term_to_string
                                                            inames2))
                                                      (fun uu___3 ->
                                                         (fun uu___3 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (43)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (43)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    inames1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Cannot combine then and else branches (different inames "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x ")")))))
                                                                 (fun uu___4
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                           uu___3)))
                                                (fun uu___3 ->
                                                   (fun uu___3 ->
                                                      Obj.magic
                                                        (Pulse_Typing_Env.fail
                                                           g
                                                           FStar_Pervasives_Native.None
                                                           uu___3)) uu___3)))
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
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (40))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (42))
                                                         (Prims.of_int (43)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (39))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (42))
                                                         (Prims.of_int (43)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.If.fst"
                                                               (Prims.of_int (42))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (42))
                                                               (Prims.of_int (42)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.If.fst"
                                                               (Prims.of_int (40))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (42))
                                                               (Prims.of_int (43)))))
                                                      (Obj.magic
                                                         (Pulse_Syntax_Printer.term_to_string
                                                            inames2))
                                                      (fun uu___3 ->
                                                         (fun uu___3 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (43)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (43)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    inames1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Cannot combine then and else branches (different inames "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x ")")))))
                                                                 (fun uu___4
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                           uu___3)))
                                                (fun uu___3 ->
                                                   (fun uu___3 ->
                                                      Obj.magic
                                                        (Pulse_Typing_Env.fail
                                                           g
                                                           FStar_Pervasives_Native.None
                                                           uu___3)) uu___3)))
                                  | (Pulse_Syntax_Base.C_ST uu___,
                                     Pulse_Syntax_Base.C_STAtomic
                                     (inames, uu___1)) ->
                                      Obj.repr
                                        (if
                                           Pulse_Syntax_Base.eq_tm inames
                                             Pulse_Syntax_Base.tm_emp_inames
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
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (52))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (53))
                                                         (Prims.of_int (42)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (51))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (53))
                                                         (Prims.of_int (42)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.If.fst"
                                                               (Prims.of_int (53))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (53))
                                                               (Prims.of_int (41)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "prims.fst"
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic
                                                         (Pulse_Syntax_Printer.term_to_string
                                                            inames))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              Prims.strcat
                                                                "Cannot lift STAtomic else branch to match ST then branch, inames "
                                                                (Prims.strcat
                                                                   uu___3
                                                                   " not empty")))))
                                                (fun uu___3 ->
                                                   (fun uu___3 ->
                                                      Obj.magic
                                                        (Pulse_Typing_Env.fail
                                                           g
                                                           FStar_Pervasives_Native.None
                                                           uu___3)) uu___3)))
                                  | (Pulse_Syntax_Base.C_STAtomic
                                     (inames, uu___), Pulse_Syntax_Base.C_ST
                                     uu___1) ->
                                      Obj.repr
                                        (if
                                           Pulse_Syntax_Base.eq_tm inames
                                             Pulse_Syntax_Base.tm_emp_inames
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
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (63))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (64))
                                                         (Prims.of_int (42)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (62))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (64))
                                                         (Prims.of_int (42)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.If.fst"
                                                               (Prims.of_int (64))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (64))
                                                               (Prims.of_int (41)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "prims.fst"
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic
                                                         (Pulse_Syntax_Printer.term_to_string
                                                            inames))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              Prims.strcat
                                                                "Cannot lift STAtomic then branch to match ST else branch, inames "
                                                                (Prims.strcat
                                                                   uu___3
                                                                   " not empty")))))
                                                (fun uu___3 ->
                                                   (fun uu___3 ->
                                                      Obj.magic
                                                        (Pulse_Typing_Env.fail
                                                           g
                                                           FStar_Pervasives_Native.None
                                                           uu___3)) uu___3)))
                                  | (Pulse_Syntax_Base.C_STGhost
                                     (uu___, uu___1), uu___2) ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.If.fst"
                                                    (Prims.of_int (66))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (66))
                                                    (Prims.of_int (82)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.If.fst"
                                                    (Prims.of_int (66))
                                                    (Prims.of_int (85))
                                                    (Prims.of_int (71))
                                                    (Prims.of_int (35)))))
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
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.If.fst"
                                                               (Prims.of_int (68))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (68))
                                                               (Prims.of_int (66)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.If.fst"
                                                               (Prims.of_int (68))
                                                               (Prims.of_int (69))
                                                               (Prims.of_int (71))
                                                               (Prims.of_int (35)))))
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
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (67)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (35)))))
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
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.If.fst"
                                                    (Prims.of_int (73))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (73))
                                                    (Prims.of_int (82)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.If.fst"
                                                    (Prims.of_int (73))
                                                    (Prims.of_int (85))
                                                    (Prims.of_int (76))
                                                    (Prims.of_int (65)))))
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
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.If.fst"
                                                               (Prims.of_int (75))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (75))
                                                               (Prims.of_int (66)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.If.fst"
                                                               (Prims.of_int (76))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (76))
                                                               (Prims.of_int (65)))))
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
                                           (Prims.strcat
                                              (Prims.strcat
                                                 "Cannot combine then and else branches (incompatible effects "
                                                 (Prims.strcat
                                                    (Pulse_Syntax_Printer.ctag_to_string
                                                       (Pulse_Syntax_Base.ctag_of_comp_st
                                                          c_then)) " and "))
                                              (Prims.strcat
                                                 (Pulse_Syntax_Printer.ctag_to_string
                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                       c_else)) " resp.)")))))
                          else
                            Obj.magic
                              (Obj.repr
                                 (Pulse_Typing_Env.fail g
                                    FStar_Pervasives_Native.None
                                    "Cannot combine then and else branches (different st_comp)")))
                         uu___)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.st_term ->
                Pulse_Syntax_Base.st_term ->
                  Pulse_Checker_Base.check_t ->
                    ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun b ->
              fun e1 ->
                fun e2 ->
                  fun check1 ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.If.fst"
                               (Prims.of_int (98)) (Prims.of_int (10))
                               (Prims.of_int (98)) (Prims.of_int (61)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.If.fst"
                               (Prims.of_int (98)) (Prims.of_int (64))
                               (Prims.of_int (160)) (Prims.of_int (43)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            Pulse_Typing_Env.push_context g "check_if"
                              e1.Pulse_Syntax_Base.range2))
                      (fun uu___ ->
                         (fun g1 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.If.fst"
                                          (Prims.of_int (101))
                                          (Prims.of_int (4))
                                          (Prims.of_int (101))
                                          (Prims.of_int (49)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.If.fst"
                                          (Prims.of_int (98))
                                          (Prims.of_int (64))
                                          (Prims.of_int (160))
                                          (Prims.of_int (43)))))
                                 (Obj.magic
                                    (Pulse_Checker_Pure.check_tot_term_with_expected_type
                                       g1 b Pulse_Typing.tm_bool))
                                 (fun uu___ ->
                                    (fun uu___ ->
                                       match uu___ with
                                       | Prims.Mkdtuple2 (b1, b_typing) ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (103))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (103))
                                                         (Prims.of_int (27)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.If.fst"
                                                         (Prims.of_int (103))
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (160))
                                                         (Prims.of_int (43)))))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___1 ->
                                                      post_hint.Pulse_Typing.post))
                                                (fun uu___1 ->
                                                   (fun post ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (19)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (43)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___1 ->
                                                                 Pulse_Typing_Env.fresh
                                                                   g1))
                                                           (fun uu___1 ->
                                                              (fun hyp ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    fun eq_v
                                                                    ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 hyp
                                                                    (Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_if_hyp")
                                                                    (Pulse_Typing.mk_eq2
                                                                    Pulse_Syntax_Pure.u0
                                                                    Pulse_Typing.tm_bool
                                                                    b1 eq_v)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    g_with_eq
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    fun eq_v
                                                                    ->
                                                                    fun br ->
                                                                    fun
                                                                    is_then
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (23)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (23)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_if_br"))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (check1
                                                                    g_with_eq1
                                                                    pre ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    ppname br))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g_with_eq1
                                                                    pre
                                                                    post_hint
                                                                    r ppname))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c,
                                                                    d) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    if
                                                                    is_then
                                                                    then
                                                                    "then"
                                                                    else
                                                                    "else"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    br_name
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
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (br1.Pulse_Syntax_Base.range2))
                                                                    (Prims.strcat
                                                                    "check_if: branch hypothesis is in freevars of checked "
                                                                    (Prims.strcat
                                                                    br_name
                                                                    " branch"))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c,
                                                                    d)))))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    check_branch
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    Pulse_Typing.tm_true
                                                                    e1 true))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    Pulse_Typing.tm_false
                                                                    e2 false))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (43)))))
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
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
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
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Impossible: check_if: unexpected freevar in post, please file a bug-report")
                                                                    else
                                                                    if
                                                                    Prims.op_Negation
                                                                    (((Pulse_Syntax_Base.eq_tm
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c)
                                                                    post_hint.Pulse_Typing.ret_ty)
                                                                    &&
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c)
                                                                    post_hint.Pulse_Typing.u))
                                                                    &&
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)
                                                                    post_hint.Pulse_Typing.post))
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (114)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    post_hint.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    post_hint.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    fun x3 ->
                                                                    fun x4 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_if: computation type after combining branches does not match post hint,computed: ("
                                                                    (Prims.strcat
                                                                    (Pulse_Syntax_Printer.univ_to_string
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c)) ", "))
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    ", "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    "), expected ("))
                                                                    (Prims.strcat
                                                                    x2 ", "))
                                                                    (Prims.strcat
                                                                    x3 ", "))
                                                                    (Prims.strcat
                                                                    x4 ")")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___7))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    (Pulse_Syntax_Printer.univ_to_string
                                                                    post_hint.Pulse_Typing.u)))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    uu___6))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6
                                                                    uu___5))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___5))
                                                                    uu___5))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.post_hint_typing
                                                                    g1
                                                                    post_hint
                                                                    x))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    post_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.intro_comp_typing
                                                                    g1 c ()
                                                                    () x ()))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.If.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    c
                                                                    (Pulse_Syntax_Base.Tm_If
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b1;
                                                                    Pulse_Syntax_Base.then_
                                                                    = e11;
                                                                    Pulse_Syntax_Base.else_
                                                                    = e21;
                                                                    Pulse_Syntax_Base.post1
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })), c,
                                                                    (Pulse_Typing.T_If
                                                                    (g1, b1,
                                                                    e11, e21,
                                                                    c,
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    c), hyp,
                                                                    (),
                                                                    e1_typing1,
                                                                    e2_typing1,
                                                                    ())))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g1 pre
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    d
                                                                    res_ppname))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                uu___1)))
                                                     uu___1))) uu___))) uu___)