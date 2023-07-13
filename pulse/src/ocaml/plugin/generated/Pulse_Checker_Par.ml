open Prims
let (check_par :
  Prims.bool ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit Pulse_Typing.post_hint_opt ->
              Prims.bool ->
                (Prims.bool -> Pulse_Checker_Common.check_t) ->
                  ((unit, unit, unit, unit)
                     Pulse_Checker_Common.checker_result_t,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun allow_inst ->
    fun g ->
      fun t ->
        fun pre ->
          fun pre_typing ->
            fun post_hint ->
              fun frame_pre ->
                fun check' ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                             (Prims.of_int (26)) (Prims.of_int (2))
                             (Prims.of_int (27)) (Prims.of_int (50)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                             (Prims.of_int (27)) (Prims.of_int (51))
                             (Prims.of_int (54)) (Prims.of_int (50)))))
                    (if Prims.op_Negation frame_pre
                     then
                       FStar_Tactics_V2_Derived.fail
                         "par: frame_pre false not supported"
                     else
                       FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
                    (fun uu___ ->
                       (fun uu___ ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (28))
                                        (Prims.of_int (10))
                                        (Prims.of_int (28))
                                        (Prims.of_int (44)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Par.fst"
                                        (Prims.of_int (28))
                                        (Prims.of_int (47))
                                        (Prims.of_int (54))
                                        (Prims.of_int (50)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     Pulse_Checker_Pure.push_context
                                       "check_par" t.Pulse_Syntax_Base.range2
                                       g))
                               (fun uu___1 ->
                                  (fun g1 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (50))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (56)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Par.fst"
                                                   (Prims.of_int (28))
                                                   (Prims.of_int (47))
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (50)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                t.Pulse_Syntax_Base.term1))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | Pulse_Syntax_Base.Tm_Par
                                                    {
                                                      Pulse_Syntax_Base.pre1
                                                        = preL;
                                                      Pulse_Syntax_Base.body11
                                                        = eL;
                                                      Pulse_Syntax_Base.post11
                                                        = postL;
                                                      Pulse_Syntax_Base.pre2
                                                        = preR;
                                                      Pulse_Syntax_Base.body21
                                                        = eR;
                                                      Pulse_Syntax_Base.post2
                                                        = postR;_}
                                                    ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Par.fst"
                                                                  (Prims.of_int (32))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (32))
                                                                  (Prims.of_int (49)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Par.fst"
                                                                  (Prims.of_int (30))
                                                                  (Prims.of_int (59))
                                                                  (Prims.of_int (54))
                                                                  (Prims.of_int (50)))))
                                                         (Obj.magic
                                                            (Pulse_Checker_Pure.check_term_with_expected_type
                                                               g1 preL
                                                               Pulse_Syntax_Base.tm_vprop))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               match uu___2
                                                               with
                                                               | Prims.Mkdtuple2
                                                                   (preL1,
                                                                    preL_typing)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_term_with_expected_type
                                                                    g1 preR
                                                                    Pulse_Syntax_Base.tm_vprop))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (preR1,
                                                                    preR_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    postL))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    postL_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1 eL
                                                                    preL1 ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    postL_hint)
                                                                    frame_pre))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eL1, cL,
                                                                    eL_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.uu___is_C_ST
                                                                    cL
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g1 eL1 cL
                                                                    eL_typing))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    cL_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.intro_post_hint
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    postR))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    postR_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (check'
                                                                    allow_inst
                                                                    g1 eR
                                                                    preR1 ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    postR_hint)
                                                                    frame_pre))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eR1, cR,
                                                                    eR_typing)
                                                                    ->
                                                                    if
                                                                    (Pulse_Syntax_Base.uu___is_C_ST
                                                                    cR) &&
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    cL)
                                                                    (Pulse_Syntax_Base.comp_u
                                                                    cR))
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g1 eR1 cR
                                                                    eR_typing))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    cR_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_Par
                                                                    (g1, eL1,
                                                                    cL, eR1,
                                                                    cR, x,
                                                                    cL_typing,
                                                                    cR_typing,
                                                                    eL_typing,
                                                                    eR_typing)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Common.try_frame_pre
                                                                    g
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre1
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.body11
                                                                    = eL1;
                                                                    Pulse_Syntax_Base.post11
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.pre2
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.body21
                                                                    = eR1;
                                                                    Pulse_Syntax_Base.post2
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown
                                                                    })) pre
                                                                    ()
                                                                    (Pulse_Typing.comp_par
                                                                    cL cR x)
                                                                    d))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Common.repack
                                                                    g pre
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre1
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.body11
                                                                    = eL1;
                                                                    Pulse_Syntax_Base.post11
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.pre2
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown;
                                                                    Pulse_Syntax_Base.body21
                                                                    = eR1;
                                                                    Pulse_Syntax_Base.post2
                                                                    =
                                                                    Pulse_Syntax_Base.tm_unknown
                                                                    }))
                                                                    uu___6
                                                                    post_hint))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (eR1.Pulse_Syntax_Base.range2))
                                                                    "par: cR is not stt"))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5))
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (eL1.Pulse_Syntax_Base.range2))
                                                                    "par: cL is not stt"))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                              uu___2)))
                                               uu___1))) uu___1))) uu___)