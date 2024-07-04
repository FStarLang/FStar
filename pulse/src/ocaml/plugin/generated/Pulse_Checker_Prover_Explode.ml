open Prims
let (has_structure : Pulse_Syntax_Base.slprop -> Prims.bool) =
  fun q ->
    match Pulse_Syntax_Pure.inspect_term q with
    | Pulse_Syntax_Pure.Tm_Star (uu___, uu___1) -> true
    | uu___ -> false
let (__explode1 :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop ->
      ((Pulse_Syntax_Base.slprop Prims.list, unit) Prims.dtuple2
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun q ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   if has_structure q
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.Mkdtuple2
                          ((Pulse_Syntax_Pure.slprop_as_list q), ()))
                   else FStar_Pervasives_Native.None))) uu___1 uu___
let (explode1 :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.slprop ->
        ((Pulse_Syntax_Base.slprop Prims.list, unit) Prims.dtuple2
           FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun q ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.Explode.fst"
                   (Prims.of_int (65)) (Prims.of_int (13))
                   (Prims.of_int (65)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.Explode.fst"
                   (Prims.of_int (66)) (Prims.of_int (2)) (Prims.of_int (66))
                   (Prims.of_int (43)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                Pulse_Checker_Prover_Base.op_Array_Access
                  pst.Pulse_Checker_Prover_Base.ss q))
          (fun uu___ ->
             (fun q_ss ->
                Obj.magic
                  (__explode1
                     (Pulse_Typing_Env.push_env
                        pst.Pulse_Checker_Prover_Base.pg
                        pst.Pulse_Checker_Prover_Base.uvs) q_ss)) uu___)
let rec (explode_aux :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Prims.bool ->
        Pulse_Syntax_Base.slprop Prims.list ->
          Pulse_Syntax_Base.slprop Prims.list ->
            ((Pulse_Syntax_Base.slprop Prims.list * Prims.bool), unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun preamble ->
               fun pst ->
                 fun prog ->
                   fun acc ->
                     fun todo ->
                       match todo with
                       | [] ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ -> (acc, prog))))
                       | q::qs ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Explode.fst"
                                            (Prims.of_int (78))
                                            (Prims.of_int (6))
                                            (Prims.of_int (80))
                                            (Prims.of_int (26)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Explode.fst"
                                            (Prims.of_int (76))
                                            (Prims.of_int (12))
                                            (Prims.of_int (82))
                                            (Prims.of_int (51)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.Explode.fst"
                                                  (Prims.of_int (78))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (78))
                                                  (Prims.of_int (26)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.Explode.fst"
                                                  (Prims.of_int (78))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (80))
                                                  (Prims.of_int (26)))))
                                         (Obj.magic (explode1 preamble pst q))
                                         (fun uu___ ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 match uu___ with
                                                 | FStar_Pervasives_Native.Some
                                                     (Prims.Mkdtuple2
                                                     (qs1, uu___2)) ->
                                                     (qs1, true)
                                                 | FStar_Pervasives_Native.None
                                                     -> ([q], false)))))
                                   (fun uu___ ->
                                      (fun uu___ ->
                                         match uu___ with
                                         | (acc', prog') ->
                                             Obj.magic
                                               (explode_aux preamble pst
                                                  (prog || prog')
                                                  (FStar_List_Tot_Base.append
                                                     acc acc') qs)) uu___))))
              uu___4 uu___3 uu___2 uu___1 uu___
let (explode :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.Explode.fst"
                 (Prims.of_int (88)) (Prims.of_int (27)) (Prims.of_int (88))
                 (Prims.of_int (70)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.Explode.fst"
                 (Prims.of_int (87)) Prims.int_one (Prims.of_int (97))
                 (Prims.of_int (3)))))
        (Obj.magic
           (explode_aux preamble pst false []
              pst.Pulse_Checker_Prover_Base.remaining_ctxt))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (remaining_ctxt, p1) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Explode.fst"
                                (Prims.of_int (89)) (Prims.of_int (22))
                                (Prims.of_int (89)) (Prims.of_int (59)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Explode.fst"
                                (Prims.of_int (88)) (Prims.of_int (73))
                                (Prims.of_int (97)) (Prims.of_int (3)))))
                       (Obj.magic
                          (explode_aux preamble pst false []
                             pst.Pulse_Checker_Prover_Base.unsolved))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               match uu___1 with
                               | (unsolved', p2) ->
                                   {
                                     Pulse_Checker_Prover_Base.pg =
                                       (pst.Pulse_Checker_Prover_Base.pg);
                                     Pulse_Checker_Prover_Base.remaining_ctxt
                                       = remaining_ctxt;
                                     Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                       = ();
                                     Pulse_Checker_Prover_Base.uvs =
                                       (pst.Pulse_Checker_Prover_Base.uvs);
                                     Pulse_Checker_Prover_Base.ss =
                                       (pst.Pulse_Checker_Prover_Base.ss);
                                     Pulse_Checker_Prover_Base.nts =
                                       (pst.Pulse_Checker_Prover_Base.nts);
                                     Pulse_Checker_Prover_Base.solved =
                                       (pst.Pulse_Checker_Prover_Base.solved);
                                     Pulse_Checker_Prover_Base.unsolved =
                                       unsolved';
                                     Pulse_Checker_Prover_Base.k =
                                       (pst.Pulse_Checker_Prover_Base.k);
                                     Pulse_Checker_Prover_Base.goals_inv = ();
                                     Pulse_Checker_Prover_Base.solved_inv =
                                       ();
                                     Pulse_Checker_Prover_Base.progress =
                                       (p1 || p2);
                                     Pulse_Checker_Prover_Base.allow_ambiguous
                                       =
                                       (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                                   })))) uu___)