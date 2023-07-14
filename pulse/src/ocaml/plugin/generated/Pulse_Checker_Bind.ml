open Prims
let (mk_bind' :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            Pulse_Syntax_Base.comp_st ->
              Pulse_Syntax_Base.nvar ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  unit ->
                    (unit, unit, unit) Pulse_Typing.st_typing ->
                      unit Pulse_Typing.post_hint_opt ->
                        unit ->
                          ((unit, unit, unit, unit)
                             Pulse_Checker_Common.checker_result_t,
                            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun e1 ->
        fun e2 ->
          fun c1 ->
            fun c2 ->
              fun px ->
                fun d_e1 ->
                  fun d_c1res ->
                    fun d_e2 ->
                      fun post_hint ->
                        fun uu___ ->
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Bind.fst"
                                     (Prims.of_int (36)) (Prims.of_int (16))
                                     (Prims.of_int (36)) (Prims.of_int (18)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Bind.fst"
                                     (Prims.of_int (36)) (Prims.of_int (4))
                                     (Prims.of_int (44)) (Prims.of_int (6)))))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> px))
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  match uu___1 with
                                  | (uu___2, x) ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Bind.fst"
                                                    (Prims.of_int (37))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (37))
                                                    (Prims.of_int (32)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Bind.fst"
                                                    (Prims.of_int (38))
                                                    (Prims.of_int (5))
                                                    (Prims.of_int (44))
                                                    (Prims.of_int (6)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 ->
                                                 Pulse_Syntax_Base.st_comp_of_comp
                                                   c2))
                                           (fun uu___3 ->
                                              (fun s2 ->
                                                 if
                                                   FStar_Set.mem x
                                                     (Pulse_Syntax_Naming.freevars
                                                        s2.Pulse_Syntax_Base.post)
                                                 then
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Bind.fst"
                                                                 (Prims.of_int (39))
                                                                 (Prims.of_int (22))
                                                                 (Prims.of_int (39))
                                                                 (Prims.of_int (121)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Bind.fst"
                                                                 (Prims.of_int (39))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (39))
                                                                 (Prims.of_int (121)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (120)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                              (Obj.magic
                                                                 (Pulse_Syntax_Printer.term_to_string
                                                                    s2.Pulse_Syntax_Base.post))
                                                              (fun uu___3 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Bound variable "
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    x)
                                                                    " escapes scope in postcondition "))
                                                                    (Prims.strcat
                                                                    uu___3 "")))))
                                                        (fun uu___3 ->
                                                           (fun uu___3 ->
                                                              Obj.magic
                                                                (Pulse_Typing_Env.fail
                                                                   g
                                                                   FStar_Pervasives_Native.None
                                                                   uu___3))
                                                             uu___3))
                                                 else
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Bind.fst"
                                                                 (Prims.of_int (41))
                                                                 (Prims.of_int (37))
                                                                 (Prims.of_int (41))
                                                                 (Prims.of_int (78)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Bind.fst"
                                                                 (Prims.of_int (40))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (44))
                                                                 (Prims.of_int (6)))))
                                                        (Obj.magic
                                                           (Pulse_Typing_Combinators.bind_res_and_post_typing
                                                              g s2 x
                                                              post_hint))
                                                        (fun uu___4 ->
                                                           (fun uu___4 ->
                                                              match uu___4
                                                              with
                                                              | (res_typing,
                                                                 post_typing)
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Combinators.mk_bind
                                                                    g pre e1
                                                                    e2 c1 c2
                                                                    px d_e1
                                                                    () d_e2
                                                                    () ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)))))
                                                             uu___4))) uu___3)))
                                 uu___1)
let (check_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Typing.post_hint_opt ->
            Prims.bool ->
              Pulse_Checker_Common.check_t ->
                ((unit, unit, unit, unit)
                   Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun frame_pre ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                           (Prims.of_int (56)) (Prims.of_int (2))
                           (Prims.of_int (57)) (Prims.of_int (55)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                           (Prims.of_int (57)) (Prims.of_int (56))
                           (Prims.of_int (78)) (Prims.of_int (5)))))
                  (if Prims.op_Negation frame_pre
                   then
                     FStar_Tactics_V2_Derived.fail
                       "check_bind: frame_pre is false, bailing"
                   else FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
                  (fun uu___ ->
                     (fun uu___ ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Bind.fst"
                                      (Prims.of_int (58)) (Prims.of_int (47))
                                      (Prims.of_int (58)) (Prims.of_int (53)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Bind.fst"
                                      (Prims.of_int (57)) (Prims.of_int (56))
                                      (Prims.of_int (78)) (Prims.of_int (5)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> t.Pulse_Syntax_Base.term1))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   match uu___1 with
                                   | Pulse_Syntax_Base.Tm_Bind
                                       { Pulse_Syntax_Base.binder = b;
                                         Pulse_Syntax_Base.head1 = e1;
                                         Pulse_Syntax_Base.body1 = e2;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Bind.fst"
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (25))
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (65)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Bind.fst"
                                                     (Prims.of_int (58))
                                                     (Prims.of_int (56))
                                                     (Prims.of_int (78))
                                                     (Prims.of_int (5)))))
                                            (Obj.magic
                                               (check g e1 pre ()
                                                  FStar_Pervasives_Native.None
                                                  frame_pre))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  match uu___2 with
                                                  | FStar_Pervasives.Mkdtuple3
                                                      (e11, c1, d1) ->
                                                      if
                                                        Prims.op_Negation
                                                          (Pulse_Syntax_Base.stateful_comp
                                                             c1)
                                                      then
                                                        Obj.magic
                                                          (Pulse_Typing_Env.fail
                                                             g
                                                             FStar_Pervasives_Native.None
                                                             "Bind: c1 is not st")
                                                      else
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (31)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (5)))))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1))
                                                             (fun uu___4 ->
                                                                (fun s1 ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    s1.Pulse_Syntax_Base.res))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                                    g
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c1)
                                                                    (Pulse_Typing_Metatheory.comp_typing_inversion
                                                                    g c1
                                                                    (Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g e11 c1
                                                                    d1))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (t_typing,
                                                                    uu___5,
                                                                    x,
                                                                    next_pre_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    s1.Pulse_Syntax_Base.post
                                                                    px))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    next_pre
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    s1.Pulse_Syntax_Base.res))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px)
                                                                    next_pre
                                                                    ()
                                                                    post_hint
                                                                    frame_pre))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e2', c2,
                                                                    d2) ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c2)
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Bind: c2 is not st")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e2' x))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    Obj.magic
                                                                    (mk_bind'
                                                                    g pre e11
                                                                    e2_closed
                                                                    c1 c2 px
                                                                    d1 () d2
                                                                    post_hint
                                                                    ()))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                  uu___4)))
                                                 uu___2))) uu___1))) uu___)
let (check_tot_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Typing.post_hint_opt ->
            Prims.bool ->
              Pulse_Checker_Common.check_t ->
                ((unit, unit, unit, unit)
                   Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun frame_pre ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                           (Prims.of_int (83)) (Prims.of_int (2))
                           (Prims.of_int (84)) (Prims.of_int (59)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                           (Prims.of_int (84)) (Prims.of_int (60))
                           (Prims.of_int (126)) (Prims.of_int (63)))))
                  (if Prims.op_Negation frame_pre
                   then
                     FStar_Tactics_V2_Derived.fail
                       "check_tot_bind: frame_pre is false, bailing"
                   else FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
                  (fun uu___ ->
                     (fun uu___ ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Bind.fst"
                                      (Prims.of_int (85)) (Prims.of_int (40))
                                      (Prims.of_int (85)) (Prims.of_int (46)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Bind.fst"
                                      (Prims.of_int (84)) (Prims.of_int (60))
                                      (Prims.of_int (126))
                                      (Prims.of_int (63)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> t.Pulse_Syntax_Base.term1))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   match uu___1 with
                                   | Pulse_Syntax_Base.Tm_TotBind
                                       { Pulse_Syntax_Base.head2 = e1;
                                         Pulse_Syntax_Base.body2 = e2;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Bind.fst"
                                                     (Prims.of_int (86))
                                                     (Prims.of_int (48))
                                                     (Prims.of_int (86))
                                                     (Prims.of_int (72)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Bind.fst"
                                                     (Prims.of_int (85))
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (126))
                                                     (Prims.of_int (63)))))
                                            (Obj.magic
                                               (Pulse_Checker_Pure.check_term_and_type
                                                  g e1))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  match uu___2 with
                                                  | FStar_Pervasives.Mkdtuple5
                                                      (e11, u1, t1,
                                                       _t1_typing, e1_typing)
                                                      ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (21)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (63)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___3 ->
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
                                                           (fun uu___3 ->
                                                              (fun t11 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g e11 t11))
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
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (63)))))
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
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
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
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_vprop_with_core
                                                                    g' pre))
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
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    (check g'
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px)
                                                                    pre ()
                                                                    post_hint
                                                                    frame_pre))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e21, c2,
                                                                    e2_typing)
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c2)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e21.Pulse_Syntax_Base.range2))
                                                                    "Tm_TotBind: e2 is not a stateful computation"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_TotBind
                                                                    {
                                                                    Pulse_Syntax_Base.head2
                                                                    = e12;
                                                                    Pulse_Syntax_Base.body2
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    e21 x)
                                                                    })),
                                                                    (Pulse_Syntax_Naming.open_comp_with
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c2 x) e12),
                                                                    (Pulse_Typing.T_TotBind
                                                                    (g, e12,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    e21 x),
                                                                    t11, c2,
                                                                    x, (),
                                                                    e2_typing)))))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                uu___3)))
                                                 uu___2))) uu___1))) uu___)
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (check_bindv2 :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Typing.post_hint_opt ->
            Prims.bool ->
              Pulse_Checker_Common.check_t ->
                ((unit, unit, unit, unit)
                   Pulse_Checker_Common.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun frame_pre ->
              fun check ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                           (Prims.of_int (150)) (Prims.of_int (2))
                           (Prims.of_int (151)) (Prims.of_int (59)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Bind.fst"
                           (Prims.of_int (151)) (Prims.of_int (60))
                           (Prims.of_int (200)) (Prims.of_int (47)))))
                  (if Prims.op_Negation frame_pre
                   then
                     FStar_Tactics_V2_Derived.fail
                       "check_bindv2: frame_pre is not set, bailing"
                   else FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
                  (fun uu___ ->
                     (fun uu___ ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Bind.fst"
                                      (Prims.of_int (153))
                                      (Prims.of_int (47))
                                      (Prims.of_int (153))
                                      (Prims.of_int (53)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Bind.fst"
                                      (Prims.of_int (151))
                                      (Prims.of_int (60))
                                      (Prims.of_int (200))
                                      (Prims.of_int (47)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> t.Pulse_Syntax_Base.term1))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   match uu___1 with
                                   | Pulse_Syntax_Base.Tm_Bind
                                       { Pulse_Syntax_Base.binder = b;
                                         Pulse_Syntax_Base.head1 = e1;
                                         Pulse_Syntax_Base.body1 = e2;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Bind.fst"
                                                     (Prims.of_int (159))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (159))
                                                     (Prims.of_int (42)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Bind.fst"
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (199))
                                                     (Prims.of_int (19)))))
                                            (Obj.magic
                                               (check g e1 pre ()
                                                  FStar_Pervasives_Native.None
                                                  false))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  match uu___2 with
                                                  | FStar_Pervasives.Mkdtuple3
                                                      (e11, c1, d1) ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (34)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___3 ->
                                                                 Pulse_Typing_Env.mk_env
                                                                   (Pulse_Typing_Env.fstar_env
                                                                    g)))
                                                           (fun uu___3 ->
                                                              (fun uvs ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    c1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun c10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover.prove
                                                                    g pre ()
                                                                    uvs
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c1) ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (g1,
                                                                    uvs1,
                                                                    ss1,
                                                                    remaining_pre,
                                                                    k) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
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
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
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
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    (Pulse_Prover_Substs.nt_subst_term
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1) ss1)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun g2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Prover_Common.op_Star
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Prover_Substs.nt_subst_term
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c1) ss1)
                                                                    px)
                                                                    remaining_pre))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre_e2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (check g2
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px)
                                                                    pre_e2 ()
                                                                    (Pulse_Prover_Common.extend_post_hint_opt_g
                                                                    g
                                                                    post_hint
                                                                    g2)
                                                                    frame_pre))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e21, c2,
                                                                    d2) ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c2)
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Bind: c2 is not st")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Prover_Common.st_typing_weakening
                                                                    g uvs e11
                                                                    c1 d1 g1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Prover_Common.st_typing_weakening_end
                                                                    g1 uvs
                                                                    e11 c1
                                                                    d11 uvs1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Prover_Substs.st_typing_nt_substs_derived
                                                                    g1 uvs1
                                                                    e11 c1
                                                                    d12 ss1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Combinators.add_frame
                                                                    g1
                                                                    (Pulse_Prover_Substs.nt_subst_st_term
                                                                    e11 ss1)
                                                                    (Pulse_Prover_Substs.nt_subst_comp
                                                                    c1 ss1)
                                                                    d13
                                                                    remaining_pre
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e12,
                                                                    c11, d14)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e21 x))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (121)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Bind.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (mk_bind'
                                                                    g1
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c11) e12
                                                                    e2_closed
                                                                    c11 c2 px
                                                                    (coerce_eq
                                                                    d14 ())
                                                                    ()
                                                                    (coerce_eq
                                                                    d2 ())
                                                                    post_hint
                                                                    ()))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (k
                                                                    post_hint
                                                                    r))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                uu___3)))
                                                 uu___2))) uu___1))) uu___)