open Prims
let (check_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Checker_Base.check_t ->
                ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                           (Prims.of_int (26)) (Prims.of_int (10))
                           (Prims.of_int (26)) (Prims.of_int (62)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                           (Prims.of_int (28)) (Prims.of_int (2))
                           (Prims.of_int (71)) (Prims.of_int (3)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Typing_Env.push_context g "check_bind"
                          t.Pulse_Syntax_Base.range2))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Bind.fst"
                                      (Prims.of_int (28)) (Prims.of_int (2))
                                      (Prims.of_int (29)) (Prims.of_int (66)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Bind.fst"
                                      (Prims.of_int (31)) (Prims.of_int (2))
                                      (Prims.of_int (71)) (Prims.of_int (3)))))
                             (Obj.magic
                                (Pulse_Checker_Prover_Util.debug_prover g1
                                   (fun uu___ ->
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Bind.fst"
                                                 (Prims.of_int (29))
                                                 (Prims.of_int (42))
                                                 (Prims.of_int (29))
                                                 (Prims.of_int (65)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "prims.fst"
                                                 (Prims.of_int (590))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (590))
                                                 (Prims.of_int (31)))))
                                        (Obj.magic
                                           (Pulse_Syntax_Printer.st_term_to_string
                                              t))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                Prims.strcat
                                                  "checking bind:\n"
                                                  (Prims.strcat uu___1 "\n"))))))
                             (fun uu___ ->
                                (fun uu___ ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Bind.fst"
                                                 (Prims.of_int (31))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (32))
                                                 (Prims.of_int (89)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Bind.fst"
                                                 (Prims.of_int (32))
                                                 (Prims.of_int (90))
                                                 (Prims.of_int (71))
                                                 (Prims.of_int (3)))))
                                        (if
                                           FStar_Pervasives_Native.uu___is_None
                                             post_hint
                                         then
                                           Obj.magic
                                             (Obj.repr
                                                (Pulse_Typing_Env.fail g1
                                                   (FStar_Pervasives_Native.Some
                                                      (t.Pulse_Syntax_Base.range2))
                                                   "check_bind: post hint is not set, please add an annotation"))
                                         else
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 -> ()))))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Bind.fst"
                                                            (Prims.of_int (34))
                                                            (Prims.of_int (45))
                                                            (Prims.of_int (34))
                                                            (Prims.of_int (51)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Bind.fst"
                                                            (Prims.of_int (32))
                                                            (Prims.of_int (90))
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (3)))))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         t.Pulse_Syntax_Base.term1))
                                                   (fun uu___2 ->
                                                      (fun uu___2 ->
                                                         match uu___2 with
                                                         | Pulse_Syntax_Base.Tm_Bind
                                                             {
                                                               Pulse_Syntax_Base.binder
                                                                 = binder;
                                                               Pulse_Syntax_Base.head1
                                                                 = e1;
                                                               Pulse_Syntax_Base.body1
                                                                 = e2;_}
                                                             ->
                                                             if
                                                               Pulse_Syntax_Base.uu___is_Tm_Admit
                                                                 e1.Pulse_Syntax_Base.term1
                                                             then
                                                               Obj.magic
                                                                 (check g1
                                                                    ctxt ()
                                                                    post_hint
                                                                    res_ppname
                                                                    e1)
                                                             else
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (7)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (3)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (check g1
                                                                    ctxt ()
                                                                    FStar_Pervasives_Native.None
                                                                    binder.Pulse_Syntax_Base.binder_ppname
                                                                    e1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    binder.Pulse_Syntax_Base.binder_ty))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (11)))))
                                                                    (match 
                                                                    ty.Pulse_Syntax_Base.t
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Unknown
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ())))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (108)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.compute_tot_term_type
                                                                    g1 ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (ty1,
                                                                    uu___6,
                                                                    uu___7)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    r))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (uu___9,
                                                                    uu___10,
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (uu___11,
                                                                    t1,
                                                                    uu___12),
                                                                    uu___13,
                                                                    uu___14)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    ty1 t1)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (108)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (107)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (108)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    t1))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (108)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (86)))))
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
                                                                    ty1))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Type mismatch: expected "
                                                                    (Prims.strcat
                                                                    uu___16
                                                                    ", got "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    uu___16
                                                                    uu___15))))
                                                                    uu___15)))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e1.Pulse_Syntax_Base.range2))
                                                                    uu___15))
                                                                    uu___15)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    -> ()))))
                                                                    uu___8)))
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    r))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, g11,
                                                                    uu___5,
                                                                    Prims.Mkdtuple2
                                                                    (ctxt',
                                                                    ctxt'_typing),
                                                                    k1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_bind_c"))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    (check
                                                                    g11 ctxt'
                                                                    ()
                                                                    post_hint
                                                                    ppname
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2
                                                                    ((binder.Pulse_Syntax_Base.binder_ppname),
                                                                    x))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g11 ctxt'
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    post_hint)
                                                                    r ppname))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (k1
                                                                    post_hint
                                                                    d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g1 ctxt
                                                                    post_hint
                                                                    d1
                                                                    res_ppname))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___4)))
                                                        uu___2))) uu___1)))
                                  uu___))) uu___)
let (check_tot_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
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
            fun t ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                           (Prims.of_int (84)) (Prims.of_int (10))
                           (Prims.of_int (84)) (Prims.of_int (66)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                           (Prims.of_int (86)) (Prims.of_int (2))
                           (Prims.of_int (139)) (Prims.of_int (3)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Typing_Env.push_context g "check_tot_bind"
                          t.Pulse_Syntax_Base.range2))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Bind.fst"
                                      (Prims.of_int (86)) (Prims.of_int (2))
                                      (Prims.of_int (87)) (Prims.of_int (93)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Bind.fst"
                                      (Prims.of_int (87)) (Prims.of_int (94))
                                      (Prims.of_int (139)) (Prims.of_int (3)))))
                             (if
                                FStar_Pervasives_Native.uu___is_None
                                  post_hint
                              then
                                Obj.magic
                                  (Obj.repr
                                     (Pulse_Typing_Env.fail g1
                                        (FStar_Pervasives_Native.Some
                                           (t.Pulse_Syntax_Base.range2))
                                        "check_tot_bind: post hint is not set, please add an annotation"))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 -> ()))))
                             (fun uu___ ->
                                (fun uu___ ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Bind.fst"
                                                 (Prims.of_int (90))
                                                 (Prims.of_int (50))
                                                 (Prims.of_int (90))
                                                 (Prims.of_int (56)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Bind.fst"
                                                 (Prims.of_int (87))
                                                 (Prims.of_int (94))
                                                 (Prims.of_int (139))
                                                 (Prims.of_int (3)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              t.Pulse_Syntax_Base.term1))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | Pulse_Syntax_Base.Tm_TotBind
                                                  {
                                                    Pulse_Syntax_Base.binder1
                                                      = b;
                                                    Pulse_Syntax_Base.head2 =
                                                      e1;
                                                    Pulse_Syntax_Base.body2 =
                                                      e2;_}
                                                  ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Bind.fst"
                                                                (Prims.of_int (91))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (91))
                                                                (Prims.of_int (55)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Bind.fst"
                                                                (Prims.of_int (91))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (139))
                                                                (Prims.of_int (3)))))
                                                       (Obj.magic
                                                          (Pulse_Checker_Base.is_stateful_application
                                                             g1 e1))
                                                       (fun uu___2 ->
                                                          (fun uu___2 ->
                                                             match uu___2
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 st_app ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = st_app;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (t.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (t.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (check_bind
                                                                    g1 pre ()
                                                                    post_hint
                                                                    res_ppname
                                                                    t1 check))
                                                                    uu___3))
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    b.Pulse_Syntax_Base.binder_ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ty
                                                                    ->
                                                                    match 
                                                                    ty.Pulse_Syntax_Base.t
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Unknown
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Pure.compute_term_type_and_u
                                                                    g1 e1)
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (108)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.compute_tot_term_type
                                                                    g1 ty))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (ty1,
                                                                    uu___5,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (108)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g1 ty1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u1,
                                                                    ty_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (108)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_at_type
                                                                    g1 e1 ty1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e11,
                                                                    eff1,
                                                                    e1_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (e11,
                                                                    eff1,
                                                                    ty1,
                                                                    (Prims.Mkdtuple2
                                                                    (u1, ())),
                                                                    ())))))
                                                                    uu___7)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (e11,
                                                                    eff1, t1,
                                                                    Prims.Mkdtuple2
                                                                    (u1,
                                                                    _t1_typing),
                                                                    e1_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Pure.tm_refine
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t1;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    }
                                                                    (Pulse_Typing.mk_eq2
                                                                    u1 t1
                                                                    (Pulse_Syntax_Pure.null_bvar
                                                                    Prims.int_zero)
                                                                    e11)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun t11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term
                                                                    g1 e11
                                                                    eff1 t11))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (e12,
                                                                    e1_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = t11;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    =
                                                                    (b.Pulse_Syntax_Base.binder_ppname)
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun b1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.continuation_elaborator_with_let
                                                                    g pre ()
                                                                    e12 eff1
                                                                    t11 b1 ()
                                                                    (Pulse_Syntax_Base.ppname_default,
                                                                    x)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun k ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ((b1.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px) t11))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    pre_typing'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_tbind_c"))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    pre ()
                                                                    post_hint
                                                                    ppname
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g' pre
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    post_hint)
                                                                    r ppname))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (k
                                                                    post_hint
                                                                    d))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    d1
                                                                    res_ppname))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                            uu___2))) uu___1)))
                                  uu___))) uu___)