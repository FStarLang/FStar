open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (check_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Checker_Base.check_t ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun post_hint ->
          fun t ->
            fun check ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                         (Prims.of_int (27)) (Prims.of_int (10))
                         (Prims.of_int (27)) (Prims.of_int (62)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                         (Prims.of_int (29)) (Prims.of_int (2))
                         (Prims.of_int (44)) (Prims.of_int (32)))))
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
                                    (Prims.of_int (29)) (Prims.of_int (2))
                                    (Prims.of_int (30)) (Prims.of_int (66)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Bind.fst"
                                    (Prims.of_int (32)) (Prims.of_int (2))
                                    (Prims.of_int (44)) (Prims.of_int (32)))))
                           (Obj.magic
                              (Pulse_Checker_Prover_Util.debug_prover g1
                                 (fun uu___ ->
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Bind.fst"
                                               (Prims.of_int (30))
                                               (Prims.of_int (42))
                                               (Prims.of_int (30))
                                               (Prims.of_int (65)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "prims.fst"
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
                                               (Prims.of_int (32))
                                               (Prims.of_int (2))
                                               (Prims.of_int (33))
                                               (Prims.of_int (89)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Bind.fst"
                                               (Prims.of_int (33))
                                               (Prims.of_int (90))
                                               (Prims.of_int (44))
                                               (Prims.of_int (32)))))
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
                                                          (Prims.of_int (35))
                                                          (Prims.of_int (44))
                                                          (Prims.of_int (35))
                                                          (Prims.of_int (50)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Bind.fst"
                                                          (Prims.of_int (33))
                                                          (Prims.of_int (90))
                                                          (Prims.of_int (44))
                                                          (Prims.of_int (32)))))
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
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (36)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (32)))))
                                                                (Obj.magic
                                                                   (check g1
                                                                    ctxt ()
                                                                    FStar_Pervasives_Native.None
                                                                    e1))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, g11,
                                                                    uu___4,
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
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (check
                                                                    g11 ctxt'
                                                                    ()
                                                                    post_hint
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2
                                                                    ((binder.Pulse_Syntax_Base.binder_ppname),
                                                                    x))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (100)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g11 ctxt'
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    post_hint)
                                                                    r))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (k1
                                                                    post_hint
                                                                    d))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g1 ctxt
                                                                    post_hint
                                                                    d1))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___3)))
                                                      uu___2))) uu___1)))
                                uu___))) uu___)
let (check_tot_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Checker_Base.check_t ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun t ->
            fun check ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                         (Prims.of_int (55)) (Prims.of_int (10))
                         (Prims.of_int (55)) (Prims.of_int (62)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                         (Prims.of_int (57)) (Prims.of_int (2))
                         (Prims.of_int (82)) (Prims.of_int (32)))))
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
                                    (Prims.of_int (57)) (Prims.of_int (2))
                                    (Prims.of_int (58)) (Prims.of_int (93)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Bind.fst"
                                    (Prims.of_int (58)) (Prims.of_int (94))
                                    (Prims.of_int (82)) (Prims.of_int (32)))))
                           (if FStar_Pervasives_Native.uu___is_None post_hint
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
                                               (Prims.of_int (60))
                                               (Prims.of_int (40))
                                               (Prims.of_int (60))
                                               (Prims.of_int (46)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Bind.fst"
                                               (Prims.of_int (58))
                                               (Prims.of_int (94))
                                               (Prims.of_int (82))
                                               (Prims.of_int (32)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            t.Pulse_Syntax_Base.term1))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            match uu___1 with
                                            | Pulse_Syntax_Base.Tm_TotBind
                                                {
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
                                                              (Prims.of_int (61))
                                                              (Prims.of_int (48))
                                                              (Prims.of_int (61))
                                                              (Prims.of_int (72)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Bind.fst"
                                                              (Prims.of_int (60))
                                                              (Prims.of_int (49))
                                                              (Prims.of_int (82))
                                                              (Prims.of_int (32)))))
                                                     (Obj.magic
                                                        (Pulse_Checker_Pure.check_term_and_type
                                                           g1 e1))
                                                     (fun uu___2 ->
                                                        (fun uu___2 ->
                                                           match uu___2 with
                                                           | FStar_Pervasives.Mkdtuple5
                                                               (e11, u1, t1,
                                                                _t1_typing,
                                                                e1_typing)
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (21)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
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
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun t11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g1 e11
                                                                    t11))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
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
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.continuation_elaborator_with_tot_bind
                                                                    g pre ()
                                                                    e12 t11
                                                                    () x))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun k ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Base.v_as_nv
                                                                    x))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px) t11))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre_typing'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    pre ()
                                                                    post_hint
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g' pre
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
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (k
                                                                    post_hint
                                                                    d))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    d1))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                          uu___2))) uu___1)))
                                uu___))) uu___)