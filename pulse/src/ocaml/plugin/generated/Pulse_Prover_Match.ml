open Prims
let (try_match_pq :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        unit ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((Pulse_Prover_Substs.t, unit) Prims.dtuple2
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun uvs ->
                   fun p ->
                     fun p_typing ->
                       fun q ->
                         fun q_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Prims.magic ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
let (compose_ss :
  Pulse_Prover_Substs.t -> Pulse_Prover_Substs.t -> Pulse_Prover_Substs.t) =
  fun ss1 -> fun ss2 -> Prims.magic ()
let (match_step :
  Pulse_Prover_Common.preamble ->
    unit Pulse_Prover_Common.prover_state ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop Prims.list ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              unit ->
                (unit Pulse_Prover_Common.prover_state
                   FStar_Pervasives_Native.option,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun p ->
        fun remaining_ctxt' ->
          fun q ->
            fun unsolved' ->
              fun uu___ ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                           (Prims.of_int (28)) (Prims.of_int (11))
                           (Prims.of_int (28)) (Prims.of_int (21)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Prover.Match.fst"
                           (Prims.of_int (29)) (Prims.of_int (52))
                           (Prims.of_int (91)) (Prims.of_int (11)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        Pulse_Prover_Common.op_Array_Access
                          pst.Pulse_Prover_Common.ss q))
                  (fun uu___1 ->
                     (fun q_ss ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Prover.Match.fst"
                                      (Prims.of_int (31)) (Prims.of_int (11))
                                      (Prims.of_int (31)) (Prims.of_int (69)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Prover.Match.fst"
                                      (Prims.of_int (32)) Prims.int_zero
                                      (Prims.of_int (91)) (Prims.of_int (11)))))
                             (Obj.magic
                                (try_match_pq pst.Pulse_Prover_Common.pg
                                   pst.Pulse_Prover_Common.uvs p () q_ss ()))
                             (fun ropt ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     match ropt with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         (Prims.Mkdtuple2 (ss_q, veq)) ->
                                         FStar_Pervasives_Native.Some
                                           {
                                             Pulse_Prover_Common.pg =
                                               (pst.Pulse_Prover_Common.pg);
                                             Pulse_Prover_Common.remaining_ctxt
                                               = remaining_ctxt';
                                             Pulse_Prover_Common.uvs =
                                               (pst.Pulse_Prover_Common.uvs);
                                             Pulse_Prover_Common.ss =
                                               (compose_ss ss_q
                                                  pst.Pulse_Prover_Common.ss);
                                             Pulse_Prover_Common.solved =
                                               (Pulse_Prover_Common.op_Star q
                                                  pst.Pulse_Prover_Common.solved);
                                             Pulse_Prover_Common.unsolved =
                                               unsolved';
                                             Pulse_Prover_Common.k =
                                               (Prims.magic ());
                                             Pulse_Prover_Common.goals_inv =
                                               ();
                                             Pulse_Prover_Common.solved_inv =
                                               ()
                                           })))) uu___1)