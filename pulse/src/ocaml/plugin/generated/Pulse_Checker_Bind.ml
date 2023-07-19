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
                         (Prims.of_int (192)) (Prims.of_int (35)))))
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
                                    (Prims.of_int (192)) (Prims.of_int (35)))))
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
                                               (Prims.of_int (192))
                                               (Prims.of_int (35)))))
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
                                                              (Prims.of_int (192))
                                                              (Prims.of_int (35)))))
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
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
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
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (y, ty_y,
                                                                    ctxt'',
                                                                    g2, k2)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g2 ty_y))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u,
                                                                    d_ty_y)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Combinators.return_in_ctxt
                                                                    g2 y u
                                                                    ty_y
                                                                    ctxt'' ()
                                                                    post_hint))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (k2
                                                                    post_hint
                                                                    d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (k1
                                                                    post_hint
                                                                    d1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t1, c,
                                                                    d2) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun x1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x1
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)
                                                                    (Pulse_Syntax_Base.ppname_default,
                                                                    x1)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    ctxt'1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.continuation_elaborator_with_bind
                                                                    g
                                                                    Pulse_Syntax_Base.tm_emp
                                                                    c t1 d2
                                                                    () x1))
                                                                    (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x1,
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c),
                                                                    ctxt'1,
                                                                    g',
                                                                    (Pulse_Checker_Common.k_elab_equiv
                                                                    g g'
                                                                    (Pulse_Prover_Common.op_Star
                                                                    Pulse_Syntax_Base.tm_emp
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c))
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    ctxt'1
                                                                    Pulse_Syntax_Base.tm_emp)
                                                                    ctxt'1 k
                                                                    () ()))))))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                          uu___3))) uu___2)))
                                uu___1))) uu___)