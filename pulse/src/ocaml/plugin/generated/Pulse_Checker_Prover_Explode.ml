open Prims
let (has_structure : Pulse_Syntax_Base.vprop -> Prims.bool) =
  fun q ->
    match Pulse_Syntax_Pure.inspect_term q with
    | Pulse_Syntax_Pure.Tm_Star (uu___, uu___1) -> true
    | uu___ -> false
let (explode1 :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.vprop ->
        ((Pulse_Syntax_Base.vprop Prims.list, unit) Prims.dtuple2
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
                   (Prims.of_int (43)) (Prims.of_int (13))
                   (Prims.of_int (43)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.Explode.fst"
                   (Prims.of_int (51)) (Prims.of_int (2)) (Prims.of_int (58))
                   (Prims.of_int (13)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                Pulse_Checker_Prover_Base.op_Array_Access
                  pst.Pulse_Checker_Prover_Base.ss q))
          (fun uu___ ->
             (fun q_ss ->
                if has_structure q_ss
                then
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.Explode.fst"
                                   (Prims.of_int (53)) (Prims.of_int (4))
                                   (Prims.of_int (56)) (Prims.of_int (5)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.Explode.fst"
                                   (Prims.of_int (57)) (Prims.of_int (4))
                                   (Prims.of_int (57)) (Prims.of_int (43)))))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.Explode.fst"
                                         (Prims.of_int (53))
                                         (Prims.of_int (25))
                                         (Prims.of_int (56))
                                         (Prims.of_int (5)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.Explode.fst"
                                         (Prims.of_int (53))
                                         (Prims.of_int (4))
                                         (Prims.of_int (56))
                                         (Prims.of_int (5)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.Explode.fst"
                                               (Prims.of_int (54))
                                               (Prims.of_int (6))
                                               (Prims.of_int (54))
                                               (Prims.of_int (34)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.Explode.fst"
                                               (Prims.of_int (53))
                                               (Prims.of_int (25))
                                               (Prims.of_int (56))
                                               (Prims.of_int (5)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.Explode.fst"
                                                     (Prims.of_int (54))
                                                     (Prims.of_int (27))
                                                     (Prims.of_int (54))
                                                     (Prims.of_int (34)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.Explode.fst"
                                                     (Prims.of_int (54))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (54))
                                                     (Prims.of_int (34)))))
                                            (Obj.magic
                                               (Pulse_PP.pp
                                                  Pulse_PP.printable_term
                                                  q_ss))
                                            (fun uu___ ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                      (Pulse_PP.text
                                                         "Exploding") uu___))))
                                      (fun uu___ ->
                                         (fun uu___ ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.Explode.fst"
                                                          (Prims.of_int (53))
                                                          (Prims.of_int (25))
                                                          (Prims.of_int (56))
                                                          (Prims.of_int (5)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.Explode.fst"
                                                          (Prims.of_int (53))
                                                          (Prims.of_int (25))
                                                          (Prims.of_int (56))
                                                          (Prims.of_int (5)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.Explode.fst"
                                                                (Prims.of_int (55))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (55))
                                                                (Prims.of_int (45)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.Explode.fst"
                                                                (Prims.of_int (53))
                                                                (Prims.of_int (25))
                                                                (Prims.of_int (56))
                                                                (Prims.of_int (5)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Explode.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (45)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Explode.fst"
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (45)))))
                                                             (Obj.magic
                                                                (Pulse_PP.pp
                                                                   (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                   (Pulse_Syntax_Pure.vprop_as_list
                                                                    q_ss)))
                                                             (fun uu___1 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___2
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "into")
                                                                    uu___1))))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               [uu___1]))))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 -> uu___ ::
                                                         uu___1)))) uu___)))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      Obj.magic
                                        (Pulse_Typing_Env.info_doc
                                           pst.Pulse_Checker_Prover_Base.pg
                                           FStar_Pervasives_Native.None uu___))
                                     uu___)))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 ->
                                  FStar_Pervasives_Native.Some
                                    (Prims.Mkdtuple2
                                       ((Pulse_Syntax_Pure.vprop_as_list q_ss),
                                         ()))))))
                else
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> FStar_Pervasives_Native.None))))
               uu___)
let rec (explode_aux :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.vprop Prims.list ->
        Pulse_Syntax_Base.vprop Prims.list ->
          (Pulse_Syntax_Base.vprop Prims.list, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun preamble ->
             fun pst ->
               fun acc ->
                 fun todo ->
                   match todo with
                   | [] ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> acc)))
                   | q::qs ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.Explode.fst"
                                        (Prims.of_int (68))
                                        (Prims.of_int (14))
                                        (Prims.of_int (68))
                                        (Prims.of_int (84)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.Explode.fst"
                                        (Prims.of_int (69))
                                        (Prims.of_int (4))
                                        (Prims.of_int (69))
                                        (Prims.of_int (26)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Prover.Explode.fst"
                                              (Prims.of_int (68))
                                              (Prims.of_int (20))
                                              (Prims.of_int (68))
                                              (Prims.of_int (84)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Prover.Explode.fst"
                                              (Prims.of_int (68))
                                              (Prims.of_int (14))
                                              (Prims.of_int (68))
                                              (Prims.of_int (84)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Prover.Explode.fst"
                                                    (Prims.of_int (68))
                                                    (Prims.of_int (27))
                                                    (Prims.of_int (68))
                                                    (Prims.of_int (41)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Prover.Explode.fst"
                                                    (Prims.of_int (68))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (68))
                                                    (Prims.of_int (84)))))
                                           (Obj.magic
                                              (explode1 preamble pst q))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   match uu___ with
                                                   | FStar_Pervasives_Native.Some
                                                       (Prims.Mkdtuple2
                                                       (qs1, uu___2)) -> qs1
                                                   | FStar_Pervasives_Native.None
                                                       -> [q]))))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             FStar_List_Tot_Base.append acc
                                               uu___))))
                               (fun uu___ ->
                                  (fun acc1 ->
                                     Obj.magic
                                       (explode_aux preamble pst acc1 qs))
                                    uu___)))) uu___3 uu___2 uu___1 uu___
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
                 (Prims.of_int (75)) (Prims.of_int (23)) (Prims.of_int (75))
                 (Prims.of_int (60)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.Explode.fst"
                 (Prims.of_int (75)) (Prims.of_int (63)) (Prims.of_int (83))
                 (Prims.of_int (3)))))
        (Obj.magic
           (explode_aux preamble pst []
              pst.Pulse_Checker_Prover_Base.remaining_ctxt))
        (fun uu___ ->
           (fun remaining_ctxt ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.Prover.Explode.fst"
                            (Prims.of_int (76)) (Prims.of_int (18))
                            (Prims.of_int (76)) (Prims.of_int (49)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.Prover.Explode.fst"
                            (Prims.of_int (77)) (Prims.of_int (4))
                            (Prims.of_int (82)) (Prims.of_int (25)))))
                   (Obj.magic
                      (explode_aux preamble pst []
                         pst.Pulse_Checker_Prover_Base.unsolved))
                   (fun unsolved' ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           {
                             Pulse_Checker_Prover_Base.pg =
                               (pst.Pulse_Checker_Prover_Base.pg);
                             Pulse_Checker_Prover_Base.remaining_ctxt =
                               remaining_ctxt;
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
                             Pulse_Checker_Prover_Base.unsolved = unsolved';
                             Pulse_Checker_Prover_Base.k =
                               (pst.Pulse_Checker_Prover_Base.k);
                             Pulse_Checker_Prover_Base.goals_inv = ();
                             Pulse_Checker_Prover_Base.solved_inv = ();
                             Pulse_Checker_Prover_Base.progress =
                               (pst.Pulse_Checker_Prover_Base.progress);
                             Pulse_Checker_Prover_Base.allow_ambiguous =
                               (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                           })))) uu___)