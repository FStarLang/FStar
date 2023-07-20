open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (check_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Typing.post_hint_opt ->
            Pulse_Checker_Common.check_t ->
              ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun ctxt ->
        fun ctxt_typing ->
          fun post_hint ->
            fun check ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                         (Prims.of_int (149)) (Prims.of_int (2))
                         (Prims.of_int (150)) (Prims.of_int (66)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                         (Prims.of_int (152)) (Prims.of_int (2))
                         (Prims.of_int (165)) (Prims.of_int (32)))))
                (Obj.magic
                   (Pulse_Prover_Common.debug_prover g
                      (fun uu___ ->
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Bind.fst"
                                    (Prims.of_int (150)) (Prims.of_int (42))
                                    (Prims.of_int (150)) (Prims.of_int (65)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "prims.fst"
                                    (Prims.of_int (590)) (Prims.of_int (19))
                                    (Prims.of_int (590)) (Prims.of_int (31)))))
                           (Obj.magic
                              (Pulse_Syntax_Printer.st_term_to_string t))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   Prims.strcat "checking bind:\n"
                                     (Prims.strcat uu___1 "\n"))))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Bind.fst"
                                    (Prims.of_int (152)) (Prims.of_int (2))
                                    (Prims.of_int (153)) (Prims.of_int (80)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Bind.fst"
                                    (Prims.of_int (153)) (Prims.of_int (81))
                                    (Prims.of_int (165)) (Prims.of_int (32)))))
                           (if FStar_Pervasives_Native.uu___is_None post_hint
                            then
                              Obj.magic
                                (Obj.repr
                                   (Pulse_Typing_Env.fail g
                                      (FStar_Pervasives_Native.Some
                                         (t.Pulse_Syntax_Base.range2))
                                      "check_bind: post_hint is None, bailing (t:\n%s\n)"))
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
                                               (Prims.of_int (155))
                                               (Prims.of_int (44))
                                               (Prims.of_int (155))
                                               (Prims.of_int (50)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Bind.fst"
                                               (Prims.of_int (153))
                                               (Prims.of_int (81))
                                               (Prims.of_int (165))
                                               (Prims.of_int (32)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            t.Pulse_Syntax_Base.term1))
                                      (fun uu___2 ->
                                         (fun uu___2 ->
                                            match uu___2 with
                                            | Pulse_Syntax_Base.Tm_Bind
                                                {
                                                  Pulse_Syntax_Base.binder =
                                                    binder;
                                                  Pulse_Syntax_Base.head1 =
                                                    e1;
                                                  Pulse_Syntax_Base.body1 =
                                                    e2;_}
                                                ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Bind.fst"
                                                              (Prims.of_int (158))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (158))
                                                              (Prims.of_int (36)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Bind.fst"
                                                              (Prims.of_int (155))
                                                              (Prims.of_int (53))
                                                              (Prims.of_int (165))
                                                              (Prims.of_int (32)))))
                                                     (Obj.magic
                                                        (check g ctxt ()
                                                           FStar_Pervasives_Native.None
                                                           e1))
                                                     (fun uu___3 ->
                                                        (fun uu___3 ->
                                                           match uu___3 with
                                                           | FStar_Pervasives.Mkdtuple5
                                                               (x, ty, ctxt',
                                                                g1, k1)
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (86)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (32)))))
                                                                    (
                                                                    Obj.magic
                                                                    (check g1
                                                                    ctxt' ()
                                                                    post_hint
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2
                                                                    ((binder.Pulse_Syntax_Base.binder_ppname),
                                                                    x))))
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (100)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.apply_checker_result_k
                                                                    g1 ctxt'
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    post_hint)
                                                                    r))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (k1
                                                                    post_hint
                                                                    d))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.checker_result_for_st_typing
                                                                    g ctxt
                                                                    post_hint
                                                                    d1))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                          uu___3))) uu___2)))
                                uu___1))) uu___)