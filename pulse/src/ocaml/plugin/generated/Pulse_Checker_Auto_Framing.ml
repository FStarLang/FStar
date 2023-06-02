open Prims

let (step_match : Pulse_Checker_Auto_Util.prover_step_t) =
  fun g ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Checker.Auto.Framing.fst"
           (Prims.of_int (14)) (Prims.of_int (14)) (Prims.of_int (14))
           (Prims.of_int (62)))
        (FStar_Range.mk_range "Pulse.Checker.Auto.Framing.fst"
           (Prims.of_int (15)) (Prims.of_int (4)) (Prims.of_int (52))
           (Prims.of_int (28)))
        (Obj.magic
           (Pulse_Checker_Framing.all_matches g
              p.Pulse_Checker_Auto_Util.unmatched_pre
              p.Pulse_Checker_Auto_Util.remaining_ctxt))
        (fun res ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                match res.Pulse_Checker_Framing.matched with
                | [] -> FStar_Pervasives_Native.None
                | uu___1 ->
                    FStar_Pervasives_Native.Some
                      {
                        Pulse_Checker_Auto_Util.preamble =
                          (p.Pulse_Checker_Auto_Util.preamble);
                        Pulse_Checker_Auto_Util.matched_pre =
                          (Pulse_Syntax_Base.Tm_Star
                             ((Pulse_Checker_VPropEquiv.list_as_vprop
                                 res.Pulse_Checker_Framing.matched),
                               (p.Pulse_Checker_Auto_Util.matched_pre)));
                        Pulse_Checker_Auto_Util.unmatched_pre =
                          (res.Pulse_Checker_Framing.unmatched_p);
                        Pulse_Checker_Auto_Util.remaining_ctxt =
                          (res.Pulse_Checker_Framing.unmatched_q);
                        Pulse_Checker_Auto_Util.proof_steps =
                          (p.Pulse_Checker_Auto_Util.proof_steps);
                        Pulse_Checker_Auto_Util.proof_steps_typing =
                          (Pulse_Typing_Metatheory.st_typing_equiv_post g
                             (Pulse_Checker_Auto_Util.__proj__Mkprover_state__item__proof_steps
                                g p)
                             (Pulse_Checker_Auto_Util.ghost_comp
                                (Pulse_Checker_Auto_Util.__proj__Mkprover_state__item__preamble
                                   g p).Pulse_Checker_Auto_Util.ctxt
                                (Pulse_Syntax_Base.Tm_Star
                                   ((Pulse_Checker_VPropEquiv.list_as_vprop
                                       (Pulse_Checker_Auto_Util.__proj__Mkprover_state__item__remaining_ctxt
                                          g p)),
                                     (Pulse_Checker_Auto_Util.__proj__Mkprover_state__item__matched_pre
                                        g p))))
                             p.Pulse_Checker_Auto_Util.proof_steps_typing
                             (Pulse_Syntax_Base.Tm_Star
                                ((Pulse_Checker_VPropEquiv.list_as_vprop
                                    res.Pulse_Checker_Framing.unmatched_q),
                                  (Pulse_Syntax_Base.Tm_Star
                                     ((Pulse_Checker_VPropEquiv.list_as_vprop
                                         res.Pulse_Checker_Framing.matched),
                                       (p.Pulse_Checker_Auto_Util.matched_pre)))))
                             ());
                        Pulse_Checker_Auto_Util.pre_equiv = ()
                      }))