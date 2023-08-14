open Prims
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      unit ->
        ((unit, unit, unit) Pulse_Typing.comp_typing, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      fun pre_typing ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                   (Prims.of_int (14)) (Prims.of_int (12))
                   (Prims.of_int (14)) (Prims.of_int (65)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                   (Prims.of_int (14)) (Prims.of_int (69))
                   (Prims.of_int (63)) (Prims.of_int (40)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                Pulse_Typing_Env.push_context_no_range g "check_comp"))
          (fun uu___ ->
             (fun g1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                              (Prims.of_int (21)) (Prims.of_int (7))
                              (Prims.of_int (42)) (Prims.of_int (9)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                              (Prims.of_int (44)) (Prims.of_int (4))
                              (Prims.of_int (63)) (Prims.of_int (40)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           fun st ->
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Comp.fst"
                                        (Prims.of_int (21))
                                        (Prims.of_int (27))
                                        (Prims.of_int (21))
                                        (Prims.of_int (50)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Comp.fst"
                                        (Prims.of_int (21))
                                        (Prims.of_int (7))
                                        (Prims.of_int (42))
                                        (Prims.of_int (9)))))
                               (Obj.magic
                                  (Pulse_Checker_Pure.check_universe g1
                                     st.Pulse_Syntax_Base.res))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | Prims.Mkdtuple2 (u, t_u) ->
                                         if
                                           Prims.op_Negation
                                             (Pulse_Syntax_Base.eq_univ u
                                                (Pulse_Syntax_Base.comp_u c))
                                         then
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Comp.fst"
                                                         (Prims.of_int (24))
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (27))
                                                         (Prims.of_int (47)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Comp.fst"
                                                         (Prims.of_int (23))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (27))
                                                         (Prims.of_int (47)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Comp.fst"
                                                               (Prims.of_int (24))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (27))
                                                               (Prims.of_int (47)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Comp.fst"
                                                               (Prims.of_int (24))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (27))
                                                               (Prims.of_int (47)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (47)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (47)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (25))
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
                                                                    st.Pulse_Syntax_Base.res))
                                                                  (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_comp: computed universe of "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " as "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", whereas annotated as "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                            (fun uu___2 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___3
                                                                    ->
                                                                    uu___2
                                                                    (Pulse_Syntax_Printer.univ_to_string
                                                                    u)))))
                                                      (fun uu___2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              uu___2
                                                                (Pulse_Syntax_Printer.univ_to_string
                                                                   (Pulse_Syntax_Base.comp_u
                                                                    c))))))
                                                (fun uu___2 ->
                                                   (fun uu___2 ->
                                                      Obj.magic
                                                        (Pulse_Typing_Env.fail
                                                           g1
                                                           FStar_Pervasives_Native.None
                                                           uu___2)) uu___2))
                                         else
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Comp.fst"
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (18))
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (25)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Comp.fst"
                                                         (Prims.of_int (30))
                                                         (Prims.of_int (28))
                                                         (Prims.of_int (41))
                                                         (Prims.of_int (11)))))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      Pulse_Typing_Env.fresh
                                                        g1))
                                                (fun uu___3 ->
                                                   (fun x ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (28)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (11)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___3 ->
                                                                 Pulse_Syntax_Base.v_as_nv
                                                                   x))
                                                           (fun uu___3 ->
                                                              (fun px ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    st.Pulse_Syntax_Base.res))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun gx
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.core_check_tot_term
                                                                    gx
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c) px)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (ty,
                                                                    post_typing)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    ty
                                                                    Pulse_Syntax_Base.tm_vprop)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (107)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (107)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (106)))))
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
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "check_comp: ill-typed postcondition "
                                                                    (Prims.strcat
                                                                    uu___4 "")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___4))
                                                                    uu___4)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.STC
                                                                    (g1, st,
                                                                    x, (),
                                                                    (), ())))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                uu___3)))
                                                     uu___3))) uu___1)))
                     (fun uu___ ->
                        (fun check_st_comp ->
                           match c with
                           | Pulse_Syntax_Base.C_ST st ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (46))
                                             (Prims.of_int (16))
                                             (Prims.of_int (46))
                                             (Prims.of_int (32)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (47))
                                             (Prims.of_int (6))
                                             (Prims.of_int (47))
                                             (Prims.of_int (19)))))
                                    (Obj.magic (check_st_comp st))
                                    (fun stc ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___ ->
                                            Pulse_Typing.CT_ST (g1, st, stc))))
                           | Pulse_Syntax_Base.C_STAtomic (i, st) ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (49))
                                             (Prims.of_int (16))
                                             (Prims.of_int (49))
                                             (Prims.of_int (32)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (49))
                                             (Prims.of_int (35))
                                             (Prims.of_int (55))
                                             (Prims.of_int (41)))))
                                    (Obj.magic (check_st_comp st))
                                    (fun uu___ ->
                                       (fun stc ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Comp.fst"
                                                        (Prims.of_int (50))
                                                        (Prims.of_int (31))
                                                        (Prims.of_int (50))
                                                        (Prims.of_int (54)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Comp.fst"
                                                        (Prims.of_int (49))
                                                        (Prims.of_int (35))
                                                        (Prims.of_int (55))
                                                        (Prims.of_int (41)))))
                                               (Obj.magic
                                                  (Pulse_Checker_Pure.core_check_tot_term
                                                     g1 i))
                                               (fun uu___ ->
                                                  (fun uu___ ->
                                                     match uu___ with
                                                     | Prims.Mkdtuple2
                                                         (ty, i_typing) ->
                                                         if
                                                           Prims.op_Negation
                                                             (Pulse_Syntax_Base.eq_tm
                                                                ty
                                                                Pulse_Syntax_Base.tm_inames)
                                                         then
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (88)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (88)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    Pulse_Syntax_Base.tm_inames))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (36)))))
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
                                                                    i))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_comp: type of inames term "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " is "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", expected "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                                    uu___1)))
                                                                   (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___1))
                                                                    uu___1)))
                                                         else
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing.CT_STAtomic
                                                                    (g1, i,
                                                                    st, (),
                                                                    stc)))))
                                                    uu___))) uu___))
                           | Pulse_Syntax_Base.C_STGhost (i, st) ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (57))
                                             (Prims.of_int (16))
                                             (Prims.of_int (57))
                                             (Prims.of_int (32)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (57))
                                             (Prims.of_int (35))
                                             (Prims.of_int (63))
                                             (Prims.of_int (40)))))
                                    (Obj.magic (check_st_comp st))
                                    (fun uu___ ->
                                       (fun stc ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Comp.fst"
                                                        (Prims.of_int (58))
                                                        (Prims.of_int (31))
                                                        (Prims.of_int (58))
                                                        (Prims.of_int (54)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Comp.fst"
                                                        (Prims.of_int (57))
                                                        (Prims.of_int (35))
                                                        (Prims.of_int (63))
                                                        (Prims.of_int (40)))))
                                               (Obj.magic
                                                  (Pulse_Checker_Pure.core_check_tot_term
                                                     g1 i))
                                               (fun uu___ ->
                                                  (fun uu___ ->
                                                     match uu___ with
                                                     | Prims.Mkdtuple2
                                                         (ty, i_typing) ->
                                                         if
                                                           Prims.op_Negation
                                                             (Pulse_Syntax_Base.eq_tm
                                                                ty
                                                                Pulse_Syntax_Base.tm_inames)
                                                         then
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (88)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (88)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    Pulse_Syntax_Base.tm_inames))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (36)))))
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
                                                                    i))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_comp: type of inames term "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " is "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", expected "))
                                                                    (Prims.strcat
                                                                    x1 "")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                                    uu___1)))
                                                                   (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___1))
                                                                    uu___1)))
                                                         else
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing.CT_STGhost
                                                                    (g1, i,
                                                                    st, (),
                                                                    stc)))))
                                                    uu___))) uu___))) uu___)))
               uu___)