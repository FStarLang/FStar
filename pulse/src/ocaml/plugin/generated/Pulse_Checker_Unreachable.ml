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
                         (Prims.of_int (72)) (Prims.of_int (50)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> t.Pulse_Syntax_Base.range1))
                (fun uu___ ->
                   (fun rng ->
                      match post_hint with
                      | FStar_Pervasives_Native.None ->
                          Obj.magic
                            (Pulse_Typing_Env.fail g
                               (FStar_Pervasives_Native.Some
                                  (t.Pulse_Syntax_Base.range1))
                               "Expected a postcondition to be annotated when unreachable is used")
                      | FStar_Pervasives_Native.Some post ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Unreachable.fst"
                                        (Prims.of_int (43))
                                        (Prims.of_int (12))
                                        (Prims.of_int (43))
                                        (Prims.of_int (19)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Unreachable.fst"
                                        (Prims.of_int (43))
                                        (Prims.of_int (22))
                                        (Prims.of_int (72))
                                        (Prims.of_int (50)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___ -> Pulse_Typing_Env.fresh g))
                               (fun uu___ ->
                                  (fun x ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Unreachable.fst"
                                                   (Prims.of_int (44))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (44))
                                                   (Prims.of_int (22)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Unreachable.fst"
                                                   (Prims.of_int (44))
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (72))
                                                   (Prims.of_int (50)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___ ->
                                                Pulse_Syntax_Base.v_as_nv x))
                                          (fun uu___ ->
                                             (fun px ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Unreachable.fst"
                                                              (Prims.of_int (45))
                                                              (Prims.of_int (29))
                                                              (Prims.of_int (45))
                                                              (Prims.of_int (33)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Unreachable.fst"
                                                              (Prims.of_int (46))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (72))
                                                              (Prims.of_int (50)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___ -> post))
                                                     (fun uu___ ->
                                                        (fun post1 ->
                                                           if
                                                             FStar_Set.mem x
                                                               (Pulse_Syntax_Naming.freevars
                                                                  post1.Pulse_Typing.post)
                                                           then
                                                             Obj.magic
                                                               (Pulse_Typing_Env.fail
                                                                  g
                                                                  FStar_Pervasives_Native.None
                                                                  "Impossible: unexpected freevar clash in Tm_Unreachable, please file a bug-report")
                                                           else
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (30)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    match 
                                                                    Pulse_Syntax_Base.ctag_of_effect_annot
                                                                    post1.Pulse_Typing.effect_annot
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c -> c
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Pulse_Syntax_Base.STT_Atomic))
                                                                  (fun uu___1
                                                                    ->
                                                                    (fun ctag
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Typing.post_hint_typing
                                                                    g post1 x))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    post_typing_rec
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post1.Pulse_Typing.post
                                                                    px))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    post1.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun t1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    post1.Pulse_Typing.u))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun u ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    t_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    post_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t1;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (post1.Pulse_Typing.post)
                                                                    }))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun s ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Typing.STC
                                                                    (g, s, x,
                                                                    (), (),
                                                                    ())))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun stc
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Pure.wr
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "l_False"])))
                                                                    rng))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun ff
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.core_check_term_at_type
                                                                    g ff
                                                                    Pulse_Typing.tm_prop))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (eff,
                                                                    ff_typing)
                                                                    ->
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_prop_validity
                                                                    g ff ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    ff_validity
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Unreachable
                                                                    (g, s,
                                                                    ctag,
                                                                    stc, ())))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun dt
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Unreachable.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (96)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    ctag)
                                                                    Pulse_Syntax_Base.Tm_Unreachable)
                                                                    (Pulse_Typing.comp_unreachable
                                                                    ctag s)
                                                                    dt
                                                                    post_hint))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    g pre ()
                                                                    uu___3
                                                                    res_ppname))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g pre
                                                                    uu___3
                                                                    post_hint
                                                                    (Pulse_RuntimeUtils.range_of_term
                                                                    t1)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                          uu___))) uu___)))
                                    uu___))) uu___)