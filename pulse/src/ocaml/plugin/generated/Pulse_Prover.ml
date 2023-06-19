open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (prover : Pulse_Prover_Common.prover_t) =
  fun uu___ ->
    fun uu___1 ->
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> Prims.magic ()))
let (prove_precondition :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
                 (unit, unit, unit) Pulse_Typing.st_typing)
                 FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun t ->
          fun c ->
            fun t_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.fst"
                         (Prims.of_int (35)) (Prims.of_int (4))
                         (Prims.of_int (35)) (Prims.of_int (63)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.fst"
                         (Prims.of_int (36)) (Prims.of_int (6))
                         (Prims.of_int (113)) (Prims.of_int (57)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      {
                        Pulse_Prover_Common.g0 = g;
                        Pulse_Prover_Common.ctxt = ctxt;
                        Pulse_Prover_Common.ctxt_typing = ();
                        Pulse_Prover_Common.t = t;
                        Pulse_Prover_Common.c = c;
                        Pulse_Prover_Common.uvs =
                          (Pulse_Typing_Env.mk_env
                             (Pulse_Typing_Env.fstar_env g))
                      }))
                (fun uu___ ->
                   (fun preamble ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Prover.fst"
                                    (Prims.of_int (38)) (Prims.of_int (11))
                                    (Prims.of_int (38)) (Prims.of_int (25)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Prover.fst"
                                    (Prims.of_int (38)) (Prims.of_int (28))
                                    (Prims.of_int (113)) (Prims.of_int (57)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> Pulse_Prover_Substs.empty g))
                           (fun uu___ ->
                              (fun ss ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (39))
                                               (Prims.of_int (21))
                                               (Prims.of_int (39))
                                               (Prims.of_int (27)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Prover.fst"
                                               (Prims.of_int (39))
                                               (Prims.of_int (30))
                                               (Prims.of_int (113))
                                               (Prims.of_int (57)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___ ->
                                            Pulse_Syntax_Base.Tm_Emp))
                                      (fun uu___ ->
                                         (fun solved_goals ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Prover.fst"
                                                          (Prims.of_int (40))
                                                          (Prims.of_int (23))
                                                          (Prims.of_int (40))
                                                          (Prims.of_int (49)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Prover.fst"
                                                          (Prims.of_int (40))
                                                          (Prims.of_int (52))
                                                          (Prims.of_int (113))
                                                          (Prims.of_int (57)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___ ->
                                                       Pulse_Checker_VPropEquiv.vprop_as_list
                                                         (Pulse_Syntax_Base.comp_pre
                                                            c)))
                                                 (fun uu___ ->
                                                    (fun unsolved_goals ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (41)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (57)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___ ->
                                                                  Pulse_Checker_VPropEquiv.vprop_as_list
                                                                    ctxt))
                                                            (fun uu___ ->
                                                               (fun
                                                                  remaining_ctxt
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    t_typing))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    t_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    ()))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    unsolved_goals_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    ()))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    remaining_ctxt_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Prover_Util.idem_steps
                                                                    g ctxt))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    uu___ ->
                                                                    match uu___
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (steps,
                                                                    steps_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (109)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    steps_typing))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    steps_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    c_pre_inv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    Pulse_Prover_Common.ss
                                                                    = ss;
                                                                    Pulse_Prover_Common.solved_goals
                                                                    =
                                                                    solved_goals;
                                                                    Pulse_Prover_Common.unsolved_goals
                                                                    =
                                                                    unsolved_goals;
                                                                    Pulse_Prover_Common.remaining_ctxt
                                                                    =
                                                                    remaining_ctxt;
                                                                    Pulse_Prover_Common.steps
                                                                    = steps;
                                                                    Pulse_Prover_Common.t_typing
                                                                    =
                                                                    t_typing1;
                                                                    Pulse_Prover_Common.unsolved_goals_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.remaining_ctxt_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.steps_typing
                                                                    =
                                                                    steps_typing1;
                                                                    Pulse_Prover_Common.c_pre_inv
                                                                    = ();
                                                                    Pulse_Prover_Common.solved_goals_closed
                                                                    = ()
                                                                    }))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun pst
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (prover
                                                                    preamble
                                                                    pst))
                                                                    (fun pst1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    match pst1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    pst2 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Prims.magic
                                                                    ()),
                                                                    (Pulse_Prover_Util.ghost_comp
                                                                    preamble.Pulse_Prover_Common.ctxt
                                                                    (Prims.magic
                                                                    ())),
                                                                    (Prims.magic
                                                                    ())))))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___)))
                                                                    uu___)))
                                                                    uu___)))
                                                                    uu___)))
                                                                 uu___)))
                                                      uu___))) uu___))) uu___)))
                     uu___)