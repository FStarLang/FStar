open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (k_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.binder ->
        Pulse_Syntax_Base.slprop ->
          unit ->
            Pulse_Syntax_Base.term ->
              unit ->
                Pulse_Syntax_Base.slprop ->
                  unit ->
                    ((unit, unit, unit, unit)
                       Pulse_Checker_Base.continuation_elaborator,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun u ->
      fun b ->
        fun p ->
          fun ex_typing ->
            fun e ->
              fun e_typing ->
                fun frame ->
                  fun frame_typing ->
                    let uu___ =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              Pulse_Typing.wtag
                                (FStar_Pervasives_Native.Some
                                   Pulse_Syntax_Base.STT_Ghost)
                                (Pulse_Syntax_Base.Tm_IntroExists
                                   {
                                     Pulse_Syntax_Base.p5 =
                                       (Pulse_Syntax_Pure.tm_exists_sl u b p);
                                     Pulse_Syntax_Base.witnesses = [e]
                                   }))) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Pulse.Checker.Prover.IntroExists.fst"
                               (Prims.of_int (45)) (Prims.of_int (10))
                               (Prims.of_int (46)) (Prims.of_int (68)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Pulse.Checker.Prover.IntroExists.fst"
                               (Prims.of_int (46)) (Prims.of_int (71))
                               (Prims.of_int (85)) (Prims.of_int (30)))))
                      (Obj.magic uu___)
                      (fun uu___1 ->
                         (fun t ->
                            let uu___1 =
                              Obj.magic
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      Pulse_Typing.comp_intro_exists u b p e)) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.IntroExists.fst"
                                          (Prims.of_int (48))
                                          (Prims.of_int (10))
                                          (Prims.of_int (48))
                                          (Prims.of_int (35)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.IntroExists.fst"
                                          (Prims.of_int (48))
                                          (Prims.of_int (38))
                                          (Prims.of_int (85))
                                          (Prims.of_int (30)))))
                                 (Obj.magic uu___1)
                                 (fun uu___2 ->
                                    (fun c ->
                                       let uu___2 =
                                         Obj.magic
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 ->
                                                 Pulse_Typing.T_IntroExists
                                                   (g, u, b, p, e, (), (),
                                                     ()))) in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.IntroExists.fst"
                                                     (Prims.of_int (50))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (50))
                                                     (Prims.of_int (103)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.IntroExists.fst"
                                                     (Prims.of_int (53))
                                                     (Prims.of_int (45))
                                                     (Prims.of_int (85))
                                                     (Prims.of_int (30)))))
                                            (Obj.magic uu___2)
                                            (fun uu___3 ->
                                               (fun t_typing ->
                                                  let uu___3 =
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___4 ->
                                                            Pulse_Typing_Env.fresh
                                                              g)) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.IntroExists.fst"
                                                                (Prims.of_int (55))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (55))
                                                                (Prims.of_int (17)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.IntroExists.fst"
                                                                (Prims.of_int (56))
                                                                (Prims.of_int (52))
                                                                (Prims.of_int (85))
                                                                (Prims.of_int (30)))))
                                                       (Obj.magic uu___3)
                                                       (fun uu___4 ->
                                                          (fun x ->
                                                             let uu___4 =
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_pintroe")) in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (44)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (30)))))
                                                                  (Obj.magic
                                                                    uu___4)
                                                                  (fun uu___5
                                                                    ->
                                                                    (fun
                                                                    ppname ->
                                                                    let uu___5
                                                                    =
                                                                    Pulse_Checker_Base.continuation_elaborator_with_bind
                                                                    g frame
                                                                    (Pulse_Typing.comp_intro_exists
                                                                    u b p e)
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Ghost)
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.p5
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_exists_sl
                                                                    u b p);
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = [e]
                                                                    }))
                                                                    t_typing
                                                                    ()
                                                                    (ppname,
                                                                    x) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun k ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun
                                                                    post_hint
                                                                    ->
                                                                    fun r ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    r)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t1, c1,
                                                                    d1) ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> d1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun d11
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing_Env.mk_env
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    empty_env
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing_Metatheory.st_typing_weakening
                                                                    g
                                                                    empty_env
                                                                    t1 c1 d11
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun d12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    g
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    frame
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    p
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    e)]))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    frame
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    p
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    e)]))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.tm_exists_sl
                                                                    u b p)
                                                                    frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    frame
                                                                    (Pulse_Syntax_Pure.tm_exists_sl
                                                                    u b p)) k
                                                                    () ()
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (t1, c1,
                                                                    d12))))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))))
                                                                    uu___5)))
                                                            uu___4))) uu___3)))
                                      uu___2))) uu___1)
let (intro_exists :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.binder ->
          Pulse_Syntax_Base.slprop ->
            Pulse_Syntax_Base.slprop Prims.list ->
              unit ->
                Pulse_Checker_Prover_Base.prover_t ->
                  (unit Pulse_Checker_Prover_Base.prover_state, unit)
                    FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun u ->
        fun b ->
          fun body ->
            fun unsolved' ->
              fun uu___ ->
                fun prover ->
                  let uu___1 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 ->
                            Pulse_Typing_Env.fresh
                              (Pulse_Typing_Env.push_env
                                 pst.Pulse_Checker_Prover_Base.pg
                                 pst.Pulse_Checker_Prover_Base.uvs))) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "Pulse.Checker.Prover.IntroExists.fst"
                             (Prims.of_int (96)) (Prims.of_int (10))
                             (Prims.of_int (96)) (Prims.of_int (41)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "Pulse.Checker.Prover.IntroExists.fst"
                             (Prims.of_int (96)) (Prims.of_int (44))
                             (Prims.of_int (354)) (Prims.of_int (6)))))
                    (Obj.magic uu___1)
                    (fun uu___2 ->
                       (fun x ->
                          let uu___2 =
                            Pulse_Syntax_Base.ppname_for_uvar
                              b.Pulse_Syntax_Base.binder_ppname in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.IntroExists.fst"
                                        (Prims.of_int (97))
                                        (Prims.of_int (15))
                                        (Prims.of_int (97))
                                        (Prims.of_int (46)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.IntroExists.fst"
                                        (Prims.of_int (97))
                                        (Prims.of_int (49))
                                        (Prims.of_int (354))
                                        (Prims.of_int (6)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  (fun ppname ->
                                     let uu___3 =
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 -> (ppname, x))) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.IntroExists.fst"
                                                   (Prims.of_int (98))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (98))
                                                   (Prims.of_int (20)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.IntroExists.fst"
                                                   (Prims.of_int (98))
                                                   (Prims.of_int (23))
                                                   (Prims.of_int (354))
                                                   (Prims.of_int (6)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             (fun px ->
                                                let uu___4 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 ->
                                                          {
                                                            Pulse_Checker_Prover_Base.g0
                                                              =
                                                              (pst.Pulse_Checker_Prover_Base.pg);
                                                            Pulse_Checker_Prover_Base.ctxt
                                                              =
                                                              (Pulse_Syntax_Pure.list_as_slprop
                                                                 pst.Pulse_Checker_Prover_Base.remaining_ctxt);
                                                            Pulse_Checker_Prover_Base.frame
                                                              =
                                                              (Pulse_Checker_Prover_Base.op_Star
                                                                 preamble.Pulse_Checker_Prover_Base.frame
                                                                 (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved));
                                                            Pulse_Checker_Prover_Base.ctxt_frame_typing
                                                              = ();
                                                            Pulse_Checker_Prover_Base.goals
                                                              =
                                                              (Pulse_Checker_Prover_Base.op_Star
                                                                 (Pulse_Syntax_Naming.open_term_nv
                                                                    body px)
                                                                 (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved'))
                                                          })) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.IntroExists.fst"
                                                              (Prims.of_int (100))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (104))
                                                              (Prims.of_int (62)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.IntroExists.fst"
                                                              (Prims.of_int (105))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (354))
                                                              (Prims.of_int (6)))))
                                                     (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun preamble_sub ->
                                                           let uu___5 =
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___6
                                                                    ->
                                                                    coerce_eq
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    preamble_sub.Pulse_Checker_Prover_Base.g0
                                                                    preamble_sub.Pulse_Checker_Prover_Base.g0
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    (Pulse_Syntax_Pure.slprop_as_list
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt))
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    Pulse_Syntax_Pure.tm_emp))
                                                                    (Pulse_Checker_Base.k_elab_unit
                                                                    preamble_sub.Pulse_Checker_Prover_Base.g0
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame))
                                                                    () ()) ())) in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (18)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                (Obj.magic
                                                                   uu___5)
                                                                (fun uu___6
                                                                   ->
                                                                   (fun k_sub
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    {
                                                                    Pulse_Checker_Prover_Base.pg
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.pg);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    =
                                                                    (Pulse_Syntax_Pure.slprop_as_list
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.uvs
                                                                    =
                                                                    (Pulse_Typing_Env.push_binding
                                                                    pst.Pulse_Checker_Prover_Base.uvs
                                                                    x ppname
                                                                    b.Pulse_Syntax_Base.binder_ty);
                                                                    Pulse_Checker_Prover_Base.ss
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.ss);
                                                                    Pulse_Checker_Prover_Base.nts
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Checker_Prover_Base.solved
                                                                    =
                                                                    Pulse_Syntax_Pure.tm_emp;
                                                                    Pulse_Checker_Prover_Base.unsolved
                                                                    =
                                                                    (FStar_List_Tot_Base.append
                                                                    (Pulse_Syntax_Pure.slprop_as_list
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    body px))
                                                                    unsolved');
                                                                    Pulse_Checker_Prover_Base.k
                                                                    = k_sub;
                                                                    Pulse_Checker_Prover_Base.goals_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.solved_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.progress
                                                                    = false;
                                                                    Pulse_Checker_Prover_Base.allow_ambiguous
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    pst_sub
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    prover
                                                                    preamble_sub
                                                                    pst_sub in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    pst_sub1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    pst_sub_goals_inv
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    match 
                                                                    pst_sub1.Pulse_Checker_Prover_Base.nts
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    nts ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> nts)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    Pulse_Checker_Prover_Substs.ss_to_nt_substs
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    pst_sub1.Pulse_Checker_Prover_Base.uvs
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun r ->
                                                                    match r
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    msg ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    FStar_Pervasives_Native.None
                                                                    (Prims.strcat
                                                                    "resulted substitution after intro exists protocol is not well-typed: "
                                                                    (Prims.strcat
                                                                    msg ""))))
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    nt ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> nt))))
                                                                    uu___11))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (nt,
                                                                    effect_labels)
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    uu___10)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    pst_sub_goals_inv1
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    pst_sub_goals_inv2
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    pst_sub_goals_inv3
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    pst_sub1.Pulse_Checker_Prover_Base.k)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    k_sub1 ->
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Pulse_Checker_Base.k_elab_equiv
                                                                    preamble_sub.Pulse_Checker_Prover_Base.g0
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    pst_sub1.Pulse_Checker_Prover_Base.solved))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    preamble_sub.Pulse_Checker_Prover_Base.goals))
                                                                    k_sub1 ()
                                                                    ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    k_sub2 ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    coerce_eq
                                                                    k_sub2 ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    k_sub3 ->
                                                                    let uu___19
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    witness
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    coerce_eq
                                                                    k_sub3 ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    k_sub4 ->
                                                                    let uu___21
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Pulse_Checker_Base.k_elab_equiv
                                                                    preamble_sub.Pulse_Checker_Prover_Base.g0
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    body)
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    witness)])
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved'))))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    body)
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    k_sub4 ()
                                                                    ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    k_sub5 ->
                                                                    let uu___22
                                                                    =
                                                                    k_intro_exists
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    u
                                                                    (Pulse_Checker_Prover_Substs.nt_subst_binder
                                                                    b nt)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    body) ()
                                                                    witness
                                                                    ()
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved')))
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.IntroExists.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    k_intro_exists1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    {
                                                                    Pulse_Checker_Prover_Base.pg
                                                                    =
                                                                    (pst_sub1.Pulse_Checker_Prover_Base.pg);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    =
                                                                    (pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.uvs
                                                                    =
                                                                    (pst_sub1.Pulse_Checker_Prover_Base.uvs);
                                                                    Pulse_Checker_Prover_Base.ss
                                                                    =
                                                                    (pst_sub1.Pulse_Checker_Prover_Base.ss);
                                                                    Pulse_Checker_Prover_Base.nts
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (nt,
                                                                    effect_labels)));
                                                                    Pulse_Checker_Prover_Base.solved
                                                                    =
                                                                    (preamble.Pulse_Checker_Prover_Base.goals);
                                                                    Pulse_Checker_Prover_Base.unsolved
                                                                    = [];
                                                                    Pulse_Checker_Prover_Base.k
                                                                    =
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    preamble.Pulse_Checker_Prover_Base.g0
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.unsolved))))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    preamble.Pulse_Checker_Prover_Base.goals))
                                                                    (Pulse_Checker_Base.k_elab_trans
                                                                    preamble.Pulse_Checker_Prover_Base.g0
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__pg
                                                                    preamble
                                                                    pst)
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__remaining_ctxt
                                                                    preamble
                                                                    pst))
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__ss
                                                                    preamble
                                                                    pst)
                                                                    (Pulse_Checker_Prover_Base.__proj__Mkprover_state__item__solved
                                                                    preamble
                                                                    pst)))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.unsolved))))
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.frame
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.unsolved))))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.unsolved))))
                                                                    (coerce_eq
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    preamble_sub.Pulse_Checker_Prover_Base.g0
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    (Pulse_Syntax_Pure.tm_exists_sl
                                                                    u b body))
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved'))))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst.Pulse_Checker_Prover_Base.unsolved))))
                                                                    (Pulse_Checker_Base.k_elab_trans
                                                                    preamble_sub.Pulse_Checker_Prover_Base.g0
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble_sub.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    body)
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    (Pulse_Syntax_Pure.tm_exists_sl
                                                                    u b body))
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved'))))
                                                                    k_sub5
                                                                    (coerce_eq
                                                                    (Pulse_Checker_Base.k_elab_equiv
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    pst_sub1.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    body)
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble_sub.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    body)
                                                                    [
                                                                    FStar_Reflection_Typing.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.frame
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved)))
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved')))
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.tm_exists_sl
                                                                    u b body)))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    pst_sub1.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    pst.Pulse_Checker_Prover_Base.solved)
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.tm_exists_sl
                                                                    u b body)))
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst_sub1.Pulse_Checker_Prover_Base.ss
                                                                    (Pulse_Syntax_Pure.list_as_slprop
                                                                    unsolved'))))
                                                                    (coerce_eq
                                                                    k_intro_exists1
                                                                    ()) () ())
                                                                    ())) ()
                                                                    ()) ())
                                                                    () ()))
                                                                    () ());
                                                                    Pulse_Checker_Prover_Base.goals_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.solved_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.progress
                                                                    = false;
                                                                    Pulse_Checker_Prover_Base.allow_ambiguous
                                                                    =
                                                                    (pst_sub1.Pulse_Checker_Prover_Base.allow_ambiguous)
                                                                    }))))
                                                                    uu___22)))
                                                                    uu___21)))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                          uu___5))) uu___4)))
                                    uu___3))) uu___2)