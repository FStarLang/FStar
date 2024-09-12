open Prims
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              let uu___ =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 -> t.Pulse_Syntax_Base.range1)) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Unreachable.fst"
                         (Prims.of_int (37)) (Prims.of_int (12))
                         (Prims.of_int (37)) (Prims.of_int (19)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Unreachable.fst"
                         (Prims.of_int (38)) (Prims.of_int (2))
                         (Prims.of_int (50)) (Prims.of_int (62)))))
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun rng ->
                      match post_hint with
                      | FStar_Pervasives_Native.None ->
                          Obj.magic
                            (Pulse_Typing_Env.fail g
                               (FStar_Pervasives_Native.Some
                                  (t.Pulse_Syntax_Base.range1))
                               "Expected a postcondition to be annotated when unreachable is used")
                      | FStar_Pervasives_Native.Some post ->
                          let uu___1 =
                            Obj.magic
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 ->
                                    Pulse_Syntax_Pure.wr
                                      (FStar_Reflection_V2_Builtins.pack_ln
                                         (FStar_Reflection_V2_Data.Tv_FVar
                                            (FStar_Reflection_V2_Builtins.pack_fv
                                               ["Prims"; "l_False"]))) rng)) in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Unreachable.fst"
                                        (Prims.of_int (43))
                                        (Prims.of_int (13))
                                        (Prims.of_int (43))
                                        (Prims.of_int (30)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Unreachable.fst"
                                        (Prims.of_int (43))
                                        (Prims.of_int (33))
                                        (Prims.of_int (50))
                                        (Prims.of_int (62)))))
                               (Obj.magic uu___1)
                               (fun uu___2 ->
                                  (fun ff ->
                                     let uu___2 =
                                       Pulse_Checker_Pure.core_check_term_at_type
                                         g ff Pulse_Typing.tm_prop in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Unreachable.fst"
                                                   (Prims.of_int (44))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (44))
                                                   (Prims.of_int (85)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Unreachable.fst"
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (33))
                                                   (Prims.of_int (50))
                                                   (Prims.of_int (62)))))
                                          (Obj.magic uu___2)
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                match uu___3 with
                                                | Prims.Mkdtuple2
                                                    (eff, ff_typing) ->
                                                    if
                                                      eff <>
                                                        FStar_TypeChecker_Core.E_Total
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_V2_Derived.fail
                                                              "Impossible: False has effect Ghost"))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (let uu___5 =
                                                              Pulse_Checker_Pure.check_prop_validity
                                                                g ff () in
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (80)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (62)))))
                                                              (Obj.magic
                                                                 uu___5)
                                                              (fun uu___6 ->
                                                                 (fun
                                                                    ff_validity
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun x ->
                                                                    let uu___7
                                                                    =
                                                                    Pulse_Typing_Combinators.comp_for_post_hint
                                                                    g pre ()
                                                                    post x in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    c_typing)
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Typing.T_Unreachable
                                                                    (g, c,
                                                                    c_typing,
                                                                    ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c))
                                                                    (Pulse_Syntax_Base.Tm_Unreachable
                                                                    {
                                                                    Pulse_Syntax_Base.c
                                                                    = c
                                                                    })), c,
                                                                    d))
                                                                    res_ppname))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                   uu___6))))
                                               uu___3))) uu___2))) uu___1)