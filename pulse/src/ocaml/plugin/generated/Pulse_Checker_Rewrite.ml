open Prims
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.st_term ->
            ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun t ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Rewrite.fst"
                       (Prims.of_int (21)) (Prims.of_int (10))
                       (Prims.of_int (21)) (Prims.of_int (48)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Rewrite.fst"
                       (Prims.of_int (21)) (Prims.of_int (51))
                       (Prims.of_int (43)) (Prims.of_int (54)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Pulse_Checker_Pure.push_context "check_rewrite"
                      t.Pulse_Syntax_Base.range2 g))
              (fun uu___ ->
                 (fun g1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Rewrite.fst"
                                  (Prims.of_int (22)) (Prims.of_int (32))
                                  (Prims.of_int (22)) (Prims.of_int (38)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Rewrite.fst"
                                  (Prims.of_int (21)) (Prims.of_int (51))
                                  (Prims.of_int (43)) (Prims.of_int (54)))))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> t.Pulse_Syntax_Base.term1))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | Pulse_Syntax_Base.Tm_Rewrite
                                   { Pulse_Syntax_Base.t1 = p;
                                     Pulse_Syntax_Base.t2 = q;_}
                                   ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Rewrite.fst"
                                                 (Prims.of_int (23))
                                                 (Prims.of_int (26))
                                                 (Prims.of_int (23))
                                                 (Prims.of_int (41)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Rewrite.fst"
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (41))
                                                 (Prims.of_int (43))
                                                 (Prims.of_int (54)))))
                                        (Obj.magic
                                           (Pulse_Checker_Pure.check_vprop g1
                                              p))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | Prims.Mkdtuple2
                                                  (p1, p_typing) ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Rewrite.fst"
                                                                (Prims.of_int (24))
                                                                (Prims.of_int (26))
                                                                (Prims.of_int (24))
                                                                (Prims.of_int (41)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Rewrite.fst"
                                                                (Prims.of_int (23))
                                                                (Prims.of_int (44))
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (54)))))
                                                       (Obj.magic
                                                          (Pulse_Checker_Pure.check_vprop
                                                             g1 q))
                                                       (fun uu___2 ->
                                                          (fun uu___2 ->
                                                             match uu___2
                                                             with
                                                             | Prims.Mkdtuple2
                                                                 (q1,
                                                                  q_typing)
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (54)))))
                                                                    (if
                                                                    Pulse_Syntax_Base.eq_tm
                                                                    p1 q1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ())))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Elaborate_Pure.elab_term
                                                                    p1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    elab_p ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Elaborate_Pure.elab_term
                                                                    q1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    elab_q ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.check_equiv
                                                                    (Pulse_Typing.elab_env
                                                                    g1)
                                                                    elab_p
                                                                    elab_q))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (res,
                                                                    issues)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                                    issues))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match res
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    elab_q))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    elab_p))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    q1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (47)))))
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
                                                                    p1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "rewrite: could not prove equality of "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\nElaborations: "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x2 "\n")))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    uu___8))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___7))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    uu___6))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    uu___6))
                                                                    uu___6)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    token ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ()))))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    equiv_p_q
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (43))
                                                                    Prims.int_one
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Rewrite
                                                                    (g1, p1,
                                                                    q1, (),
                                                                    ())))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Rewrite.fst"
                                                                    (Prims.of_int (43))
                                                                    Prims.int_one
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    g pre ()
                                                                    (Pulse_Typing.wr
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t1
                                                                    = p1;
                                                                    Pulse_Syntax_Base.t2
                                                                    = q1
                                                                    }))
                                                                    (Pulse_Typing.comp_rewrite
                                                                    p1 q1) d))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.repack
                                                                    g pre
                                                                    uu___3
                                                                    post_hint
                                                                    t.Pulse_Syntax_Base.range2))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                            uu___2))) uu___1)))
                              uu___))) uu___)