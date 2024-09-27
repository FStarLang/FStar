open Prims
let (check :
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
              fun check1 ->
                let uu___ =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          Pulse_Checker_Pure.push_context "check_par"
                            t.Pulse_Syntax_Base.range1 g)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (41)) (Prims.of_int (10))
                           (Prims.of_int (41)) (Prims.of_int (44)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Par.fst"
                           (Prims.of_int (41)) (Prims.of_int (47))
                           (Prims.of_int (66)) (Prims.of_int (123)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun g1 ->
                        let uu___1 =
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> t.Pulse_Syntax_Base.term1)) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Par.fst"
                                      (Prims.of_int (43)) (Prims.of_int (50))
                                      (Prims.of_int (43)) (Prims.of_int (56)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Par.fst"
                                      (Prims.of_int (41)) (Prims.of_int (47))
                                      (Prims.of_int (66))
                                      (Prims.of_int (123)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   match uu___2 with
                                   | Pulse_Syntax_Base.Tm_Par
                                       { Pulse_Syntax_Base.pre1 = preL;
                                         Pulse_Syntax_Base.body11 = eL;
                                         Pulse_Syntax_Base.post11 = postL;
                                         Pulse_Syntax_Base.pre2 = preR;
                                         Pulse_Syntax_Base.body21 = eR;
                                         Pulse_Syntax_Base.post2 = postR;_}
                                       ->
                                       let uu___3 =
                                         Pulse_Checker_Pure.check_tot_term g1
                                           preL Pulse_Syntax_Pure.tm_slprop in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Par.fst"
                                                     (Prims.of_int (44))
                                                     (Prims.of_int (32))
                                                     (Prims.of_int (44))
                                                     (Prims.of_int (63)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Par.fst"
                                                     (Prims.of_int (43))
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (66))
                                                     (Prims.of_int (123)))))
                                            (Obj.magic uu___3)
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  match uu___4 with
                                                  | Prims.Mkdtuple2
                                                      (preL1, preL_typing) ->
                                                      let uu___5 =
                                                        Pulse_Checker_Pure.check_tot_term
                                                          g1 preR
                                                          Pulse_Syntax_Pure.tm_slprop in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (63)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (123)))))
                                                           (Obj.magic uu___5)
                                                           (fun uu___6 ->
                                                              (fun uu___6 ->
                                                                 match uu___6
                                                                 with
                                                                 | Prims.Mkdtuple2
                                                                    (preR1,
                                                                    preR_typing)
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    Pulse_Checker_Base.intro_post_hint
                                                                    g1
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    FStar_Pervasives_Native.None
                                                                    postL in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (123)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    postL_hint
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_par_l")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    ppname ->
                                                                    let uu___10
                                                                    =
                                                                    check1 g1
                                                                    preL1 ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    postL_hint)
                                                                    ppname eL in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g1 preL1
                                                                    postL_hint
                                                                    r ppname))
                                                                    uu___11)))
                                                                    uu___10) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (123)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eL1, cL,
                                                                    eL_typing)
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing_Metatheory_Base.st_typing_correctness
                                                                    g1 eL1 cL
                                                                    eL_typing)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (123)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    cL_typing
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Checker_Base.intro_post_hint
                                                                    g1
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    FStar_Pervasives_Native.None
                                                                    postR in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (123)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    postR_hint
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_par_r")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    ppname ->
                                                                    let uu___14
                                                                    =
                                                                    check1 g1
                                                                    preR1 ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    postR_hint)
                                                                    ppname eR in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g1 preR1
                                                                    postR_hint
                                                                    r ppname))
                                                                    uu___15)))
                                                                    uu___14) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (123)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (eR1, cR,
                                                                    eR_typing)
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Typing_Metatheory_Base.st_typing_correctness
                                                                    g1 eR1 cR
                                                                    eR_typing)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (123)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    cR_typing
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (123)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun x ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Pulse_Typing.T_Par
                                                                    (g1, eL1,
                                                                    cL, eR1,
                                                                    cR, x,
                                                                    cL_typing,
                                                                    cR_typing,
                                                                    eL_typing,
                                                                    eR_typing))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (123)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun d ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g1
                                                                    (Pulse_Typing.wrst
                                                                    cL
                                                                    (Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre1
                                                                    =
                                                                    Pulse_Syntax_Pure.tm_unknown;
                                                                    Pulse_Syntax_Base.body11
                                                                    = eL1;
                                                                    Pulse_Syntax_Base.post11
                                                                    =
                                                                    Pulse_Syntax_Pure.tm_unknown;
                                                                    Pulse_Syntax_Base.pre2
                                                                    =
                                                                    Pulse_Syntax_Pure.tm_unknown;
                                                                    Pulse_Syntax_Base.body21
                                                                    = eR1;
                                                                    Pulse_Syntax_Base.post2
                                                                    =
                                                                    Pulse_Syntax_Pure.tm_unknown
                                                                    }))
                                                                    (Pulse_Typing.comp_par
                                                                    cL cR x)
                                                                    d
                                                                    post_hint in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (105)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    false g
                                                                    pre ()
                                                                    uu___19
                                                                    res_ppname))
                                                                    uu___19) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (105)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Par.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (123)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g pre
                                                                    uu___18
                                                                    post_hint
                                                                    t.Pulse_Syntax_Base.range1))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                uu___6)))
                                                 uu___4))) uu___2))) uu___1)