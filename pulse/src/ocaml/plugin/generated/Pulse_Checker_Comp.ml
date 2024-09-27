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
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  Pulse_Typing_Env.push_context_no_range g "check_comp")) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                   (Prims.of_int (30)) (Prims.of_int (12))
                   (Prims.of_int (30)) (Prims.of_int (65)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                   (Prims.of_int (30)) (Prims.of_int (69))
                   (Prims.of_int (80)) (Prims.of_int (37)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun g1 ->
                let uu___1 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          fun st ->
                            let uu___3 =
                              Pulse_Checker_Pure.check_universe g1
                                st.Pulse_Syntax_Base.res in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Comp.fst"
                                       (Prims.of_int (37))
                                       (Prims.of_int (27))
                                       (Prims.of_int (37))
                                       (Prims.of_int (50)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Comp.fst"
                                       (Prims.of_int (37)) (Prims.of_int (7))
                                       (Prims.of_int (58)) (Prims.of_int (9)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    match uu___4 with
                                    | Prims.Mkdtuple2 (u, t_u) ->
                                        if
                                          Prims.op_Negation
                                            (Pulse_Syntax_Base.eq_univ u
                                               (Pulse_Syntax_Base.comp_u c))
                                        then
                                          let uu___5 =
                                            let uu___6 =
                                              let uu___7 =
                                                let uu___8 =
                                                  Pulse_Syntax_Printer.term_to_string
                                                    st.Pulse_Syntax_Base.res in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Comp.fst"
                                                           (Prims.of_int (41))
                                                           (Prims.of_int (17))
                                                           (Prims.of_int (41))
                                                           (Prims.of_int (42)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Printf.fst"
                                                           (Prims.of_int (122))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (124))
                                                           (Prims.of_int (44)))))
                                                  (Obj.magic uu___8)
                                                  (fun uu___9 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___10 ->
                                                          fun x ->
                                                            fun x1 ->
                                                              Prims.strcat
                                                                (Prims.strcat
                                                                   (Prims.strcat
                                                                    "check_comp: computed universe of "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " as "))
                                                                   (Prims.strcat
                                                                    x
                                                                    ", whereas annotated as "))
                                                                (Prims.strcat
                                                                   x1 ""))) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Comp.fst"
                                                         (Prims.of_int (40))
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (43))
                                                         (Prims.of_int (47)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Comp.fst"
                                                         (Prims.of_int (40))
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (43))
                                                         (Prims.of_int (47)))))
                                                (Obj.magic uu___7)
                                                (fun uu___8 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___9 ->
                                                        uu___8
                                                          (Pulse_Syntax_Printer.univ_to_string
                                                             u))) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Comp.fst"
                                                       (Prims.of_int (40))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (43))
                                                       (Prims.of_int (47)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Comp.fst"
                                                       (Prims.of_int (40))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (43))
                                                       (Prims.of_int (47)))))
                                              (Obj.magic uu___6)
                                              (fun uu___7 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___8 ->
                                                      uu___7
                                                        (Pulse_Syntax_Printer.univ_to_string
                                                           (Pulse_Syntax_Base.comp_u
                                                              c)))) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Comp.fst"
                                                        (Prims.of_int (40))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (43))
                                                        (Prims.of_int (47)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Comp.fst"
                                                        (Prims.of_int (39))
                                                        (Prims.of_int (13))
                                                        (Prims.of_int (43))
                                                        (Prims.of_int (47)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun uu___6 ->
                                                     Obj.magic
                                                       (Pulse_Typing_Env.fail
                                                          g1
                                                          FStar_Pervasives_Native.None
                                                          uu___6)) uu___6))
                                        else
                                          (let uu___6 =
                                             Obj.magic
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___7 ->
                                                     Pulse_Typing_Env.fresh
                                                       g1)) in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Comp.fst"
                                                         (Prims.of_int (46))
                                                         (Prims.of_int (18))
                                                         (Prims.of_int (46))
                                                         (Prims.of_int (25)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Comp.fst"
                                                         (Prims.of_int (46))
                                                         (Prims.of_int (28))
                                                         (Prims.of_int (57))
                                                         (Prims.of_int (11)))))
                                                (Obj.magic uu___6)
                                                (fun uu___7 ->
                                                   (fun x ->
                                                      let uu___7 =
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___8 ->
                                                                Pulse_Syntax_Base.v_as_nv
                                                                  x)) in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (28)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (11)))))
                                                           (Obj.magic uu___7)
                                                           (fun uu___8 ->
                                                              (fun px ->
                                                                 let uu___8 =
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px)
                                                                    st.Pulse_Syntax_Base.res)) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun gx
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Pulse_Checker_Pure.core_compute_tot_term_type
                                                                    gx
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c) px) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
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
                                                                    Pulse_Syntax_Pure.tm_slprop)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    "check_comp: ill-typed postcondition "
                                                                    (Prims.strcat
                                                                    uu___13
                                                                    ""))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (107)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (107)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___12))
                                                                    uu___12)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing.STC
                                                                    (g1, st,
                                                                    x, (),
                                                                    (), ())))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                uu___8)))
                                                     uu___7)))) uu___4))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                              (Prims.of_int (37)) (Prims.of_int (7))
                              (Prims.of_int (58)) (Prims.of_int (9)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Comp.fst"
                              (Prims.of_int (60)) (Prims.of_int (4))
                              (Prims.of_int (80)) (Prims.of_int (37)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun check_st_comp ->
                           match c with
                           | Pulse_Syntax_Base.C_ST st ->
                               let uu___2 = check_st_comp st in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (62))
                                             (Prims.of_int (16))
                                             (Prims.of_int (62))
                                             (Prims.of_int (32)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (63))
                                             (Prims.of_int (6))
                                             (Prims.of_int (63))
                                             (Prims.of_int (19)))))
                                    (Obj.magic uu___2)
                                    (fun stc ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            Pulse_Typing.CT_ST (g1, st, stc))))
                           | Pulse_Syntax_Base.C_STAtomic (i, obs, st) ->
                               let uu___2 = check_st_comp st in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (65))
                                             (Prims.of_int (16))
                                             (Prims.of_int (65))
                                             (Prims.of_int (32)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (65))
                                             (Prims.of_int (35))
                                             (Prims.of_int (71))
                                             (Prims.of_int (45)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun stc ->
                                          let uu___3 =
                                            Pulse_Checker_Pure.core_compute_tot_term_type
                                              g1 i in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Comp.fst"
                                                        (Prims.of_int (66))
                                                        (Prims.of_int (31))
                                                        (Prims.of_int (66))
                                                        (Prims.of_int (61)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Comp.fst"
                                                        (Prims.of_int (65))
                                                        (Prims.of_int (35))
                                                        (Prims.of_int (71))
                                                        (Prims.of_int (45)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun uu___4 ->
                                                     match uu___4 with
                                                     | Prims.Mkdtuple2
                                                         (ty, i_typing) ->
                                                         if
                                                           Prims.op_Negation
                                                             (Pulse_Syntax_Base.eq_tm
                                                                ty
                                                                Pulse_Syntax_Pure.tm_inames)
                                                         then
                                                           Obj.magic
                                                             (Obj.repr
                                                                (let uu___5 =
                                                                   let uu___6
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    Pulse_Syntax_Pure.tm_inames in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    i in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_comp (atomic): type of inames term "
                                                                    (Prims.strcat
                                                                    uu___13
                                                                    " is "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", expected "))
                                                                    (Prims.strcat
                                                                    x1 ""))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    uu___12
                                                                    uu___10))))
                                                                    uu___10) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    uu___7))))
                                                                    uu___7) in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (88)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (88)))))
                                                                   (Obj.magic
                                                                    uu___5)
                                                                   (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___6))
                                                                    uu___6)))
                                                         else
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.CT_STAtomic
                                                                    (g1, i,
                                                                    obs, st,
                                                                    (), stc)))))
                                                    uu___4))) uu___3))
                           | Pulse_Syntax_Base.C_STGhost (i, st) ->
                               let uu___2 =
                                 Pulse_Checker_Pure.core_compute_tot_term_type
                                   g1 i in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (73))
                                             (Prims.of_int (31))
                                             (Prims.of_int (73))
                                             (Prims.of_int (61)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Comp.fst"
                                             (Prims.of_int (72))
                                             (Prims.of_int (23))
                                             (Prims.of_int (80))
                                             (Prims.of_int (37)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          match uu___3 with
                                          | Prims.Mkdtuple2 (ty, i_typing) ->
                                              if
                                                Prims.op_Negation
                                                  (Pulse_Syntax_Base.eq_tm ty
                                                     Pulse_Syntax_Pure.tm_inames)
                                              then
                                                let uu___4 =
                                                  let uu___5 =
                                                    Pulse_Syntax_Printer.term_to_string
                                                      Pulse_Syntax_Pure.tm_inames in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Comp.fst"
                                                             (Prims.of_int (77))
                                                             (Prims.of_int (59))
                                                             (Prims.of_int (77))
                                                             (Prims.of_int (87)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Comp.fst"
                                                             (Prims.of_int (76))
                                                             (Prims.of_int (13))
                                                             (Prims.of_int (77))
                                                             (Prims.of_int (88)))))
                                                    (Obj.magic uu___5)
                                                    (fun uu___6 ->
                                                       (fun uu___6 ->
                                                          let uu___7 =
                                                            let uu___8 =
                                                              Pulse_Syntax_Printer.term_to_string
                                                                ty in
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (58)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (88)))))
                                                              (Obj.magic
                                                                 uu___8)
                                                              (fun uu___9 ->
                                                                 (fun uu___9
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Syntax_Printer.term_to_string
                                                                    i in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_comp (ghost): type of inames term "
                                                                    (Prims.strcat
                                                                    uu___12
                                                                    " is "))
                                                                    (Prims.strcat
                                                                    x
                                                                    ", expected "))
                                                                    (Prims.strcat
                                                                    x1 ""))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    uu___11
                                                                    uu___9))))
                                                                   uu___9) in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (88)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Comp.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (88)))))
                                                               (Obj.magic
                                                                  uu___7)
                                                               (fun uu___8 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___6))))
                                                         uu___6) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Comp.fst"
                                                              (Prims.of_int (76))
                                                              (Prims.of_int (13))
                                                              (Prims.of_int (77))
                                                              (Prims.of_int (88)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Comp.fst"
                                                              (Prims.of_int (75))
                                                              (Prims.of_int (11))
                                                              (Prims.of_int (77))
                                                              (Prims.of_int (88)))))
                                                     (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun uu___5 ->
                                                           Obj.magic
                                                             (Pulse_Typing_Env.fail
                                                                g1
                                                                FStar_Pervasives_Native.None
                                                                uu___5))
                                                          uu___5))
                                              else
                                                (let uu___5 =
                                                   check_st_comp st in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Comp.fst"
                                                               (Prims.of_int (79))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (79))
                                                               (Prims.of_int (34)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Comp.fst"
                                                               (Prims.of_int (80))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (80))
                                                               (Prims.of_int (37)))))
                                                      (Obj.magic uu___5)
                                                      (fun stc ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___6 ->
                                                              Pulse_Typing.CT_STGhost
                                                                (g1, i, st,
                                                                  (), stc))))))
                                         uu___3))) uu___2))) uu___1)