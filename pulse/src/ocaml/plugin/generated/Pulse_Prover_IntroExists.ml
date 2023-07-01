open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let (k_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.binder ->
        Pulse_Syntax_Base.vprop ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.vprop ->
              ((unit, unit, unit, unit)
                 Pulse_Prover_Common.continuation_elaborator,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun u ->
                   fun b ->
                     fun p ->
                       fun e ->
                         fun frame ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Prims.magic ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
let (intro_exists :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.binder ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              unit ->
                Pulse_Prover_Common.prover_t ->
                  (unit Pulse_Prover_Common.prover_state, unit)
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
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "Pulse.Prover.IntroExists.fst"
                             (Prims.of_int (29)) (Prims.of_int (10))
                             (Prims.of_int (29)) (Prims.of_int (22)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "Pulse.Prover.IntroExists.fst"
                             (Prims.of_int (29)) (Prims.of_int (25))
                             (Prims.of_int (257)) (Prims.of_int (6)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          Pulse_Typing_Env.fresh pst.Pulse_Prover_Common.pg))
                    (fun uu___1 ->
                       (fun x ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.IntroExists.fst"
                                        (Prims.of_int (30))
                                        (Prims.of_int (11))
                                        (Prims.of_int (30))
                                        (Prims.of_int (29)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.IntroExists.fst"
                                        (Prims.of_int (30))
                                        (Prims.of_int (32))
                                        (Prims.of_int (257))
                                        (Prims.of_int (6)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     ((b.Pulse_Syntax_Base.binder_ppname), x)))
                               (fun uu___1 ->
                                  (fun px ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.IntroExists.fst"
                                                   (Prims.of_int (32))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (36))
                                                   (Prims.of_int (61)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.IntroExists.fst"
                                                   (Prims.of_int (37))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (257))
                                                   (Prims.of_int (6)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                {
                                                  Pulse_Prover_Common.g0 =
                                                    (pst.Pulse_Prover_Common.pg);
                                                  Pulse_Prover_Common.ctxt =
                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                       pst.Pulse_Prover_Common.remaining_ctxt);
                                                  Pulse_Prover_Common.frame =
                                                    (Pulse_Prover_Common.op_Star
                                                       preamble.Pulse_Prover_Common.frame
                                                       (Pulse_Prover_Common.op_Array_Access
                                                          pst.Pulse_Prover_Common.ss
                                                          pst.Pulse_Prover_Common.solved));
                                                  Pulse_Prover_Common.ctxt_frame_typing
                                                    = ();
                                                  Pulse_Prover_Common.goals =
                                                    (Pulse_Prover_Common.op_Star
                                                       (Pulse_Syntax_Naming.open_term_nv
                                                          body px)
                                                       (Pulse_Checker_VPropEquiv.list_as_vprop
                                                          unsolved'))
                                                }))
                                          (fun uu___1 ->
                                             (fun preamble_sub ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.IntroExists.fst"
                                                              (Prims.of_int (41))
                                                              (Prims.of_int (105))
                                                              (Prims.of_int (50))
                                                              (Prims.of_int (18)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.IntroExists.fst"
                                                              (Prims.of_int (51))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (257))
                                                              (Prims.of_int (6)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           coerce_eq
                                                             (Pulse_Prover_Common.k_elab_equiv
                                                                preamble_sub.Pulse_Prover_Common.g0
                                                                preamble_sub.Pulse_Prover_Common.g0
                                                                (Pulse_Prover_Common.op_Star
                                                                   preamble_sub.Pulse_Prover_Common.ctxt
                                                                   preamble_sub.Pulse_Prover_Common.frame)
                                                                (Pulse_Prover_Common.op_Star
                                                                   preamble_sub.Pulse_Prover_Common.ctxt
                                                                   preamble_sub.Pulse_Prover_Common.frame)
                                                                (Pulse_Prover_Common.op_Star
                                                                   preamble_sub.Pulse_Prover_Common.ctxt
                                                                   preamble_sub.Pulse_Prover_Common.frame)
                                                                (Pulse_Prover_Common.op_Star
                                                                   (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                    preamble_sub.Pulse_Prover_Common.ctxt))
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                   (Pulse_Prover_Common.op_Array_Access
                                                                    pst.Pulse_Prover_Common.ss
                                                                    Pulse_Syntax_Base.tm_emp))
                                                                (Pulse_Prover_Common.k_elab_unit
                                                                   preamble_sub.Pulse_Prover_Common.g0
                                                                   (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame))
                                                                () ()) ()))
                                                     (fun uu___1 ->
                                                        (fun k_sub ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (25)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___1 ->
                                                                    {
                                                                    Pulse_Prover_Common.pg
                                                                    =
                                                                    (pst.Pulse_Prover_Common.pg);
                                                                    Pulse_Prover_Common.remaining_ctxt
                                                                    =
                                                                    (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                    preamble_sub.Pulse_Prover_Common.ctxt);
                                                                    Pulse_Prover_Common.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.uvs
                                                                    =
                                                                    (pst.Pulse_Prover_Common.uvs);
                                                                    Pulse_Prover_Common.ss
                                                                    =
                                                                    (pst.Pulse_Prover_Common.ss);
                                                                    Pulse_Prover_Common.solved
                                                                    =
                                                                    Pulse_Syntax_Base.tm_emp;
                                                                    Pulse_Prover_Common.unsolved
                                                                    =
                                                                    (FStar_List_Tot_Base.append
                                                                    [
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    body px]
                                                                    unsolved');
                                                                    Pulse_Prover_Common.solved_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.k
                                                                    = k_sub;
                                                                    Pulse_Prover_Common.goals_inv
                                                                    = ()
                                                                    }))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    pst_sub
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    (prover
                                                                    preamble_sub
                                                                    pst_sub))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub_goals_inv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (68)))))
                                                                    (Obj.magic
                                                                    (Pulse_Prover_Substs.check_well_typedness
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    pst_sub1.Pulse_Prover_Common.uvs
                                                                    pst_sub1.Pulse_Prover_Common.ss))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.op_Negation
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    if uu___1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    FStar_Pervasives_Native.None
                                                                    "intro exists ss not well-typed"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                                    uu___1)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pst_sub_goals_inv1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pst_sub_goals_inv2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pst_sub_goals_inv3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    pst_sub1.Pulse_Prover_Common.k))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    k_sub1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Prover_Common.k_elab_equiv
                                                                    preamble_sub.Pulse_Prover_Common.g0
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    pst_sub1.Pulse_Prover_Common.solved))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    preamble_sub.Pulse_Prover_Common.goals))
                                                                    k_sub1 ()
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    k_sub2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    coerce_eq
                                                                    k_sub2 ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    k_sub3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    witness
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    coerce_eq
                                                                    k_sub3 ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    k_sub4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Prover_Common.k_elab_equiv
                                                                    preamble_sub.Pulse_Prover_Common.g0
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    witness)])
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved'))))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    k_sub4 ()
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    k_sub5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (25)))))
                                                                    (Obj.magic
                                                                    (k_intro_exists
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    u
                                                                    (Pulse_Prover_Substs.nt_subst_binder
                                                                    b
                                                                    (Pulse_Prover_Substs.as_nt_substs
                                                                    pst_sub1.Pulse_Prover_Common.ss))
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    witness
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))))
                                                                    (fun
                                                                    k_intro_exists1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    {
                                                                    Pulse_Prover_Common.pg
                                                                    =
                                                                    (pst_sub1.Pulse_Prover_Common.pg);
                                                                    Pulse_Prover_Common.remaining_ctxt
                                                                    =
                                                                    (pst_sub1.Pulse_Prover_Common.remaining_ctxt);
                                                                    Pulse_Prover_Common.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.uvs
                                                                    =
                                                                    (pst_sub1.Pulse_Prover_Common.uvs);
                                                                    Pulse_Prover_Common.ss
                                                                    =
                                                                    (pst_sub1.Pulse_Prover_Common.ss);
                                                                    Pulse_Prover_Common.solved
                                                                    =
                                                                    (preamble.Pulse_Prover_Common.goals);
                                                                    Pulse_Prover_Common.unsolved
                                                                    = [];
                                                                    Pulse_Prover_Common.solved_typing
                                                                    = ();
                                                                    Pulse_Prover_Common.k
                                                                    =
                                                                    (Pulse_Prover_Common.k_elab_equiv
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.ctxt
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.ctxt
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.unsolved))))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    preamble.Pulse_Prover_Common.goals))
                                                                    (Pulse_Prover_Common.k_elab_trans
                                                                    preamble.Pulse_Prover_Common.g0
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__pg
                                                                    preamble
                                                                    pst)
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.ctxt
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__remaining_ctxt
                                                                    preamble
                                                                    pst))
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__ss
                                                                    preamble
                                                                    pst)
                                                                    (Pulse_Prover_Common.__proj__Mkprover_state__item__solved
                                                                    preamble
                                                                    pst)))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.unsolved))))
                                                                    pst.Pulse_Prover_Common.k
                                                                    (Pulse_Prover_Common.k_elab_equiv
                                                                    pst.Pulse_Prover_Common.pg
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.remaining_ctxt)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.frame
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved)))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.unsolved))))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.unsolved))))
                                                                    (coerce_eq
                                                                    (Pulse_Prover_Common.k_elab_equiv
                                                                    preamble_sub.Pulse_Prover_Common.g0
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b body))
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved'))))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst.Pulse_Prover_Common.unsolved))))
                                                                    (Pulse_Prover_Common.k_elab_trans
                                                                    preamble_sub.Pulse_Prover_Common.g0
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble_sub.Pulse_Prover_Common.ctxt
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    pst.Pulse_Prover_Common.solved
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b body))
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved'))))
                                                                    k_sub5
                                                                    (coerce_eq
                                                                    (Pulse_Prover_Common.k_elab_equiv
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    pst_sub1.Pulse_Prover_Common.pg
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble_sub.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    body)
                                                                    [
                                                                    Pulse_Syntax_Naming.DT
                                                                    (Prims.int_zero,
                                                                    witness)]))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    preamble.Pulse_Prover_Common.frame
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved)))
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b body)))
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub1.Pulse_Prover_Common.remaining_ctxt)
                                                                    preamble.Pulse_Prover_Common.frame)
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Syntax_Base.tm_exists_sl
                                                                    u b body)))
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub1.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved'))))
                                                                    (coerce_eq
                                                                    k_intro_exists1
                                                                    ()) () ())
                                                                    ())) ()
                                                                    ()) ())
                                                                    () ()))
                                                                    () ());
                                                                    Pulse_Prover_Common.goals_inv
                                                                    = ()
                                                                    }))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                          uu___1))) uu___1)))
                                    uu___1))) uu___1)