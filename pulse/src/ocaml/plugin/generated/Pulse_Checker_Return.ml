open Prims
let (check_return :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Typing.post_hint_opt ->
            ((unit, unit, unit) Pulse_Checker_Common.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun st ->
      fun ctxt ->
        fun ctxt_typing ->
          fun post_hint ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                       (Prims.of_int (23)) (Prims.of_int (10))
                       (Prims.of_int (23)) (Prims.of_int (48)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Return.fst"
                       (Prims.of_int (23)) (Prims.of_int (51))
                       (Prims.of_int (45)) (Prims.of_int (56)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Checker_Pure.push_context "check_return"
                      st.Pulse_Syntax_Base.range2 g))
              (fun uu___ ->
                 (fun g1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Return.fst"
                                  (Prims.of_int (24)) (Prims.of_int (53))
                                  (Prims.of_int (24)) (Prims.of_int (60)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Return.fst"
                                  (Prims.of_int (23)) (Prims.of_int (51))
                                  (Prims.of_int (45)) (Prims.of_int (56)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> st.Pulse_Syntax_Base.term1))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | Pulse_Syntax_Base.Tm_Return
                                   { Pulse_Syntax_Base.ctag = c;
                                     Pulse_Syntax_Base.insert_eq = use_eq;
                                     Pulse_Syntax_Base.term = t;_}
                                   ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Return.fst"
                                                 (Prims.of_int (31))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (40))
                                                 (Prims.of_int (48)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Return.fst"
                                                 (Prims.of_int (24))
                                                 (Prims.of_int (63))
                                                 (Prims.of_int (45))
                                                 (Prims.of_int (56)))))
                                        (match post_hint with
                                         | FStar_Pervasives_Native.None ->
                                             Obj.magic
                                               (Pulse_Checker_Pure.check_term_and_type
                                                  g1 t)
                                         | FStar_Pervasives_Native.Some post
                                             ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Return.fst"
                                                           (Prims.of_int (34))
                                                           (Prims.of_int (23))
                                                           (Prims.of_int (34))
                                                           (Prims.of_int (68)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Return.fst"
                                                           (Prims.of_int (33))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (40))
                                                           (Prims.of_int (48)))))
                                                  (Obj.magic
                                                     (Pulse_Checker_Pure.check_term_with_expected_type
                                                        g1 t
                                                        post.Pulse_Typing.ret_ty))
                                                  (fun uu___1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          match uu___1 with
                                                          | Prims.Mkdtuple2
                                                              (t1, d) ->
                                                              FStar_Pervasives.Mkdtuple5
                                                                (t1,
                                                                  (post.Pulse_Typing.u),
                                                                  (post.Pulse_Typing.ret_ty),
                                                                  (), d)))))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | FStar_Pervasives.Mkdtuple5
                                                  (t1, u, ty, uty, d) ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Return.fst"
                                                                (Prims.of_int (41))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (45))
                                                                (Prims.of_int (56)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Return.fst"
                                                                (Prims.of_int (41))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (45))
                                                                (Prims.of_int (56)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             uu___1))
                                                       (fun uu___2 ->
                                                          (fun uu___2 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (17)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (56)))))
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                  (fun uu___3
                                                                    ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Return
                                                                    (g1, c,
                                                                    use_eq,
                                                                    u, ty,
                                                                    t1,
                                                                    Pulse_Syntax_Base.tm_emp,
                                                                    x, (),
                                                                    (), ())))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Return.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover.try_frame_pre
                                                                    g ctxt ()
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Return
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    = c;
                                                                    Pulse_Syntax_Base.insert_eq
                                                                    = use_eq;
                                                                    Pulse_Syntax_Base.term
                                                                    = t1
                                                                    }))
                                                                    (Pulse_Typing.comp_return
                                                                    c use_eq
                                                                    u ty t1
                                                                    Pulse_Syntax_Base.tm_emp
                                                                    x) d1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Prover.repack
                                                                    g ctxt
                                                                    uu___3
                                                                    post_hint
                                                                    t1.Pulse_Syntax_Base.range1))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                            uu___2))) uu___1)))
                              uu___))) uu___)