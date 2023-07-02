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
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
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
                           (Prims.of_int (88)) (Prims.of_int (11)))))
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
                                      (Prims.of_int (88)) (Prims.of_int (11)))))
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
                                             Pulse_Prover_Common.remaining_ctxt_frame_typing
                                               = ();
                                             Pulse_Prover_Common.uvs =
                                               (pst.Pulse_Prover_Common.uvs);
                                             Pulse_Prover_Common.ss =
                                               (Pulse_Prover_Substs.push
                                                  pst.Pulse_Prover_Common.ss
                                                  ss_q);
                                             Pulse_Prover_Common.solved =
                                               (Pulse_Prover_Common.op_Star q
                                                  pst.Pulse_Prover_Common.solved);
                                             Pulse_Prover_Common.unsolved =
                                               unsolved';
                                             Pulse_Prover_Common.solved_typing
                                               = ();
                                             Pulse_Prover_Common.k =
                                               (coerce_eq
                                                  (Pulse_Prover_Common.k_elab_equiv
                                                     preamble.Pulse_Prover_Common.g0
                                                     pst.Pulse_Prover_Common.pg
                                                     (Pulse_Prover_Common.op_Star
                                                        preamble.Pulse_Prover_Common.ctxt
                                                        preamble.Pulse_Prover_Common.frame)
                                                     (Pulse_Prover_Common.op_Star
                                                        preamble.Pulse_Prover_Common.ctxt
                                                        preamble.Pulse_Prover_Common.frame)
                                                     (Pulse_Prover_Common.op_Star
                                                        (Pulse_Prover_Common.op_Star
                                                           (Pulse_Checker_VPropEquiv.list_as_vprop
                                                              (p ::
                                                              remaining_ctxt'))
                                                           preamble.Pulse_Prover_Common.frame)
                                                        (Pulse_Prover_Common.op_Array_Access
                                                           (Pulse_Prover_Substs.push
                                                              pst.Pulse_Prover_Common.ss
                                                              ss_q)
                                                           pst.Pulse_Prover_Common.solved))
                                                     (Pulse_Prover_Common.op_Star
                                                        (Pulse_Prover_Common.op_Star
                                                           (Pulse_Checker_VPropEquiv.list_as_vprop
                                                              remaining_ctxt')
                                                           preamble.Pulse_Prover_Common.frame)
                                                        (Pulse_Prover_Common.op_Star
                                                           (Pulse_Prover_Common.op_Array_Access
                                                              (Pulse_Prover_Substs.push
                                                                 pst.Pulse_Prover_Common.ss
                                                                 ss_q) q)
                                                           (Pulse_Prover_Common.op_Array_Access
                                                              (Pulse_Prover_Substs.push
                                                                 pst.Pulse_Prover_Common.ss
                                                                 ss_q)
                                                              pst.Pulse_Prover_Common.solved)))
                                                     (coerce_eq
                                                        pst.Pulse_Prover_Common.k
                                                        ()) () ()) ());
                                             Pulse_Prover_Common.goals_inv =
                                               ()
                                           })))) uu___1)