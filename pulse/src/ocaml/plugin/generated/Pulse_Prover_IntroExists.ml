open Prims
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
                             (Prims.of_int (26)) (Prims.of_int (10))
                             (Prims.of_int (26)) (Prims.of_int (22)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "Pulse.Prover.IntroExists.fst"
                             (Prims.of_int (26)) (Prims.of_int (25))
                             (Prims.of_int (195)) (Prims.of_int (6)))))
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
                                        (Prims.of_int (27))
                                        (Prims.of_int (11))
                                        (Prims.of_int (27))
                                        (Prims.of_int (29)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.IntroExists.fst"
                                        (Prims.of_int (27))
                                        (Prims.of_int (32))
                                        (Prims.of_int (195))
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
                                                   (Prims.of_int (29))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (32))
                                                   (Prims.of_int (74)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.IntroExists.fst"
                                                   (Prims.of_int (34))
                                                   (Prims.of_int (37))
                                                   (Prims.of_int (195))
                                                   (Prims.of_int (6)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                {
                                                  Pulse_Prover_Common.g0 =
                                                    (pst.Pulse_Prover_Common.pg);
                                                  Pulse_Prover_Common.ctxt =
                                                    (Pulse_Prover_Common.op_Star
                                                       (Pulse_Checker_VPropEquiv.list_as_vprop
                                                          pst.Pulse_Prover_Common.remaining_ctxt)
                                                       (Pulse_Prover_Common.op_Array_Access
                                                          pst.Pulse_Prover_Common.ss
                                                          pst.Pulse_Prover_Common.solved));
                                                  Pulse_Prover_Common.ctxt_typing
                                                    = ();
                                                  Pulse_Prover_Common.goals =
                                                    (Pulse_Prover_Common.op_Star
                                                       (Pulse_Prover_Common.op_Star
                                                          pst.Pulse_Prover_Common.solved
                                                          (Pulse_Syntax_Naming.open_term_nv
                                                             body px))
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
                                                              (Prims.of_int (36))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (44))
                                                              (Prims.of_int (20)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.IntroExists.fst"
                                                              (Prims.of_int (45))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (195))
                                                              (Prims.of_int (6)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           {
                                                             Pulse_Prover_Common.pg
                                                               =
                                                               (pst.Pulse_Prover_Common.pg);
                                                             Pulse_Prover_Common.remaining_ctxt
                                                               =
                                                               (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                  preamble_sub.Pulse_Prover_Common.ctxt);
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
                                                                  (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved))
                                                                  (FStar_List_Tot_Base.append
                                                                    [
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    body px]
                                                                    unsolved'));
                                                             Pulse_Prover_Common.k
                                                               =
                                                               (Prims.magic
                                                                  ());
                                                             Pulse_Prover_Common.goals_inv
                                                               = ();
                                                             Pulse_Prover_Common.solved_inv
                                                               = ()
                                                           }))
                                                     (fun uu___1 ->
                                                        (fun pst_sub ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (39)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (6)))))
                                                                (Obj.magic
                                                                   (prover
                                                                    preamble_sub
                                                                    pst_sub))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    pst_sub_terminal
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub_terminal_goals_inv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub_terminal_goals_inv1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    pst_sub_terminal.Pulse_Prover_Common.k))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.magic
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    k_sub_terminal1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub_terminal.Pulse_Prover_Common.ss
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    witness
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.magic
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.IntroExists.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (k_intro_exists
                                                                    pst_sub_terminal.Pulse_Prover_Common.pg
                                                                    u
                                                                    (Pulse_Prover_Substs.nt_subst_binder
                                                                    b
                                                                    (Pulse_Prover_Substs.as_nt_substs
                                                                    pst_sub_terminal.Pulse_Prover_Common.ss))
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub_terminal.Pulse_Prover_Common.ss
                                                                    body)
                                                                    witness
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Prover_Common.op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub_terminal.Pulse_Prover_Common.remaining_ctxt)
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub_terminal.Pulse_Prover_Common.ss
                                                                    pst.Pulse_Prover_Common.solved))
                                                                    (Pulse_Prover_Common.op_Array_Access
                                                                    pst_sub_terminal.Pulse_Prover_Common.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))))
                                                                    (fun
                                                                    k_intro_exists1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    Pulse_Prover_Common.pg
                                                                    =
                                                                    (pst_sub_terminal.Pulse_Prover_Common.pg);
                                                                    Pulse_Prover_Common.remaining_ctxt
                                                                    =
                                                                    (pst_sub_terminal.Pulse_Prover_Common.remaining_ctxt);
                                                                    Pulse_Prover_Common.uvs
                                                                    =
                                                                    (pst_sub_terminal.Pulse_Prover_Common.uvs);
                                                                    Pulse_Prover_Common.ss
                                                                    =
                                                                    (pst_sub_terminal.Pulse_Prover_Common.ss);
                                                                    Pulse_Prover_Common.solved
                                                                    =
                                                                    (preamble.Pulse_Prover_Common.goals);
                                                                    Pulse_Prover_Common.unsolved
                                                                    = [];
                                                                    Pulse_Prover_Common.k
                                                                    =
                                                                    (Prims.magic
                                                                    ());
                                                                    Pulse_Prover_Common.goals_inv
                                                                    = ();
                                                                    Pulse_Prover_Common.solved_inv
                                                                    = ()
                                                                    }))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                          uu___1))) uu___1)))
                                    uu___1))) uu___1)