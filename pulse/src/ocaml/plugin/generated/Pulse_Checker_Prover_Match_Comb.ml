open Prims

let (wrap_matcher :
  Prims.string ->
    Pulse_Checker_Prover_Match_Base.matcher_t ->
      Pulse_Checker_Prover_Base.preamble ->
        unit Pulse_Checker_Prover_Base.prover_state ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop ->
              ((unit, unit, unit, unit)
                 Pulse_Checker_Prover_Match_Base.match_success_t
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun label ->
    fun matcher ->
      fun preamble ->
        fun pst ->
          fun p ->
            fun q ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.Match.Comb.fst"
                         (Prims.of_int (47)) (Prims.of_int (2))
                         (Prims.of_int (48)) (Prims.of_int (39)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.Match.Comb.fst"
                         (Prims.of_int (49)) (Prims.of_int (2))
                         (Prims.of_int (56)) (Prims.of_int (16)))))
                (if
                   Pulse_RuntimeUtils.debug_at_level
                     (Pulse_Typing_Env.fstar_env
                        pst.Pulse_Checker_Prover_Base.pg) "prover.match"
                 then
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_V1_Builtins.print
                           (Prims.strcat "Trying matcher " label)))
                 else
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_V2_Derived.try_with
                           (fun uu___1 ->
                              match () with
                              | () ->
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.Match.Comb.fst"
                                             (Prims.of_int (50))
                                             (Prims.of_int (9))
                                             (Prims.of_int (50))
                                             (Prims.of_int (26)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.Match.Comb.fst"
                                             (Prims.of_int (50))
                                             (Prims.of_int (4))
                                             (Prims.of_int (50))
                                             (Prims.of_int (26)))))
                                    (Obj.magic (matcher preamble pst p q))
                                    (fun uu___2 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            FStar_Pervasives_Native.Some
                                              uu___2)))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 match uu___1 with
                                 | Pulse_Checker_Prover_Match_Base.NoMatch s
                                     ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.Match.Comb.fst"
                                                      (Prims.of_int (53))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (54))
                                                      (Prims.of_int (31)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.Match.Comb.fst"
                                                      (Prims.of_int (55))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (55))
                                                      (Prims.of_int (8)))))
                                             (if
                                                Pulse_RuntimeUtils.debug_at_level
                                                  (Pulse_Typing_Env.fstar_env
                                                     pst.Pulse_Checker_Prover_Base.pg)
                                                  "prover.match"
                                              then
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_V1_Builtins.print
                                                        (Prims.strcat
                                                           "NoMatch: " s)))
                                              else
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 -> ()))))
                                             (fun uu___2 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___3 ->
                                                     FStar_Pervasives_Native.None))))
                                 | e ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.raise e)))
                                uu___1))) uu___)
let rec (match_f_1n :
  Prims.string ->
    Pulse_Checker_Prover_Match_Base.matcher_t ->
      Pulse_Checker_Prover_Base.preamble ->
        unit Pulse_Checker_Prover_Base.prover_state ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              ((Pulse_Syntax_Base.vprop, Pulse_Syntax_Base.vprop Prims.list,
                 unit, Pulse_Checker_Prover_Substs.ss_t, unit)
                 FStar_Pervasives.dtuple5 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun label ->
                 fun matcher ->
                   fun preamble ->
                     fun pst ->
                       fun q ->
                         fun ctxt0 ->
                           match ctxt0 with
                           | [] ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          FStar_Pervasives_Native.None)))
                           | p::ps ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.Match.Comb.fst"
                                                (Prims.of_int (75))
                                                (Prims.of_int (4))
                                                (Prims.of_int (80))
                                                (Prims.of_int (7)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.Match.Comb.fst"
                                                (Prims.of_int (81))
                                                (Prims.of_int (4))
                                                (Prims.of_int (120))
                                                (Prims.of_int (5)))))
                                       (if
                                          Pulse_RuntimeUtils.debug_at_level
                                            (Pulse_Typing_Env.fstar_env
                                               pst.Pulse_Checker_Prover_Base.pg)
                                            "prover.match"
                                        then
                                          Obj.magic
                                            (Obj.repr
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.Match.Comb.fst"
                                                           (Prims.of_int (76))
                                                           (Prims.of_int (22))
                                                           (Prims.of_int (76))
                                                           (Prims.of_int (51)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.Match.Comb.fst"
                                                           (Prims.of_int (76))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (80))
                                                           (Prims.of_int (7)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Prover.Match.Comb.fst"
                                                                 (Prims.of_int (76))
                                                                 (Prims.of_int (31))
                                                                 (Prims.of_int (76))
                                                                 (Prims.of_int (50)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Prover.Match.Comb.fst"
                                                                 (Prims.of_int (76))
                                                                 (Prims.of_int (22))
                                                                 (Prims.of_int (76))
                                                                 (Prims.of_int (51)))))
                                                        (Obj.magic
                                                           (Pulse_Typing_Env.range_of_env
                                                              pst.Pulse_Checker_Prover_Base.pg))
                                                        (fun uu___ ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___1 ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu___))))
                                                  (fun uu___ ->
                                                     (fun uu___ ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (7)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (7)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (7)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (7)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    p))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "p =")
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    q)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "q =")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    [uu___2]))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___1 ::
                                                                    uu___2))))
                                                                    uu___1)))
                                                                   (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (Pulse_PP.text
                                                                    "Trying to match")
                                                                    :: uu___1))))
                                                             (fun uu___1 ->
                                                                (fun uu___1
                                                                   ->
                                                                   Obj.magic
                                                                    (Pulse_Typing_Env.info_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    uu___
                                                                    uu___1))
                                                                  uu___1)))
                                                       uu___)))
                                        else
                                          Obj.magic
                                            (Obj.repr
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___1 -> ()))))
                                       (fun uu___ ->
                                          (fun uu___ ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.Match.Comb.fst"
                                                           (Prims.of_int (81))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (81))
                                                           (Prims.of_int (53)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.Match.Comb.fst"
                                                           (Prims.of_int (81))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (120))
                                                           (Prims.of_int (5)))))
                                                  (Obj.magic
                                                     (wrap_matcher label
                                                        matcher preamble pst
                                                        p
                                                        (Pulse_Checker_Prover_Base.op_Array_Access
                                                           pst.Pulse_Checker_Prover_Base.ss
                                                           q)))
                                                  (fun uu___1 ->
                                                     (fun uu___1 ->
                                                        match uu___1 with
                                                        | FStar_Pervasives_Native.Some
                                                            (Prims.Mkdtuple2
                                                            (ss_extension,
                                                             pq))
                                                            ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (9)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (59)))))
                                                                 (if
                                                                    Prims.op_Negation
                                                                    pst.Pulse_Checker_Prover_Base.allow_ambiguous
                                                                  then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (20)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    pst.Pulse_Checker_Prover_Base.pg)
                                                                    "prover.match"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V1_Builtins.print
                                                                    "Checking for ambiguity"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (match_f_1n
                                                                    label
                                                                    matcher
                                                                    preamble
                                                                    pst q ps))
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p',
                                                                    uu___4,
                                                                    uu___5,
                                                                    uu___6,
                                                                    uu___7))
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Reflection_V2_TermEq.term_eq
                                                                    p p')
                                                                    then
                                                                    FStar_Tactics_Effect.raise
                                                                    (Pulse_Checker_Prover_Match_Base.Ambig
                                                                    (q, p,
                                                                    p'))
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ())
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))))
                                                                    uu___2)))
                                                                  else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Checker_Prover_Substs.push_ss
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    ss_extension))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ss'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (59)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    pst.Pulse_Checker_Prover_Base.pg)
                                                                    "prover.match"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Env.range_of_env
                                                                    pst.Pulse_Checker_Prover_Base.pg))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "p =")
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    q)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "q =")
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_Checker_Prover_Substs.pp_ss_t
                                                                    ss'))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "ss' =")
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    ss' q)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "ss'.(q) =")
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    [uu___7]))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___6 ::
                                                                    uu___7))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___5 ::
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___4 ::
                                                                    uu___5))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (Pulse_PP.text
                                                                    (Prims.strcat
                                                                    "Matched with "
                                                                    label))
                                                                    :: uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    uu___3
                                                                    uu___4))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p, ps,
                                                                    (), ss',
                                                                    ()))))))
                                                                    uu___3)))
                                                                    uu___2))
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (45)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (5)))))
                                                                 (Obj.magic
                                                                    (
                                                                    match_f_1n
                                                                    label
                                                                    matcher
                                                                    preamble
                                                                    pst q ps))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p',
                                                                    ctxt1,
                                                                    ctxt1_ok,
                                                                    ss', p'q))
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p', (p
                                                                    ::
                                                                    ctxt1),
                                                                    (), ss',
                                                                    ()))))))
                                                       uu___1))) uu___))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let report_ambig :
  'a .
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop ->
          Pulse_Syntax_Base.vprop -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun g ->
    fun q ->
      fun p ->
        fun p' ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.Comb.fst"
                     (Prims.of_int (129)) (Prims.of_int (22))
                     (Prims.of_int (129)) (Prims.of_int (46)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.Comb.fst"
                     (Prims.of_int (129)) (Prims.of_int (2))
                     (Prims.of_int (137)) (Prims.of_int (3)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Match.Comb.fst"
                           (Prims.of_int (129)) (Prims.of_int (31))
                           (Prims.of_int (129)) (Prims.of_int (45)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Match.Comb.fst"
                           (Prims.of_int (129)) (Prims.of_int (22))
                           (Prims.of_int (129)) (Prims.of_int (46)))))
                  (Obj.magic (Pulse_Typing_Env.range_of_env g))
                  (fun uu___ ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> FStar_Pervasives_Native.Some uu___))))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Comb.fst"
                                (Prims.of_int (129)) (Prims.of_int (47))
                                (Prims.of_int (137)) (Prims.of_int (3)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.Match.Comb.fst"
                                (Prims.of_int (129)) (Prims.of_int (2))
                                (Prims.of_int (137)) (Prims.of_int (3)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.Match.Comb.fst"
                                      (Prims.of_int (130)) (Prims.of_int (4))
                                      (Prims.of_int (131))
                                      (Prims.of_int (19)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.Match.Comb.fst"
                                      (Prims.of_int (129))
                                      (Prims.of_int (47))
                                      (Prims.of_int (137)) (Prims.of_int (3)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Match.Comb.fst"
                                            (Prims.of_int (131))
                                            (Prims.of_int (6))
                                            (Prims.of_int (131))
                                            (Prims.of_int (19)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Match.Comb.fst"
                                            (Prims.of_int (130))
                                            (Prims.of_int (4))
                                            (Prims.of_int (131))
                                            (Prims.of_int (19)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.Match.Comb.fst"
                                                  (Prims.of_int (131))
                                                  (Prims.of_int (13))
                                                  (Prims.of_int (131))
                                                  (Prims.of_int (19)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.Match.Comb.fst"
                                                  (Prims.of_int (131))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (131))
                                                  (Prims.of_int (19)))))
                                         (Obj.magic
                                            (Pulse_PP.pp
                                               Pulse_PP.printable_term q))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 Pulse_PP.indent uu___1))))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           FStar_Pprint.op_Hat_Hat
                                             (Pulse_PP.text
                                                "Ambiguous match for resource:")
                                             uu___1))))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Match.Comb.fst"
                                                 (Prims.of_int (129))
                                                 (Prims.of_int (47))
                                                 (Prims.of_int (137))
                                                 (Prims.of_int (3)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Match.Comb.fst"
                                                 (Prims.of_int (129))
                                                 (Prims.of_int (47))
                                                 (Prims.of_int (137))
                                                 (Prims.of_int (3)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Prover.Match.Comb.fst"
                                                       (Prims.of_int (132))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (136))
                                                       (Prims.of_int (26)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Prover.Match.Comb.fst"
                                                       (Prims.of_int (129))
                                                       (Prims.of_int (47))
                                                       (Prims.of_int (137))
                                                       (Prims.of_int (3)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.Match.Comb.fst"
                                                             (Prims.of_int (133))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (136))
                                                             (Prims.of_int (26)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.Match.Comb.fst"
                                                             (Prims.of_int (132))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (136))
                                                             (Prims.of_int (26)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.Match.Comb.fst"
                                                                   (Prims.of_int (133))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (133))
                                                                   (Prims.of_int (19)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.Match.Comb.fst"
                                                                   (Prims.of_int (133))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (136))
                                                                   (Prims.of_int (26)))))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (19)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (19)))))
                                                                (Obj.magic
                                                                   (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    p))
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_PP.indent
                                                                    uu___2))))
                                                          (fun uu___2 ->
                                                             (fun uu___2 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    p'))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_PP.indent
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___3
                                                                    (FStar_Pprint.op_Hat_Hat
                                                                    FStar_Pprint.hardline
                                                                    (Pulse_PP.text
                                                                    "in the context."))))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "and:")
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    FStar_Pprint.hardline
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___2
                                                                    uu___3))))
                                                               uu___2)))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            FStar_Pprint.op_Hat_Hat
                                                              (Pulse_PP.text
                                                                 "It can be matched by both:")
                                                              uu___2))))
                                              (fun uu___2 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 -> [uu___2]))))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 -> uu___1 :: uu___2))))
                                  uu___1)))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (Pulse_Typing_Env.fail_doc_env true g uu___
                                  uu___1)) uu___1))) uu___)
let rec (match_f_nn :
  Prims.string ->
    Pulse_Checker_Prover_Match_Base.matcher_t ->
      Pulse_Checker_Prover_Base.preamble ->
        unit Pulse_Checker_Prover_Base.prover_state ->
          Pulse_Syntax_Base.vprop Prims.list ->
            Pulse_Syntax_Base.vprop Prims.list ->
              ((unit, unit, unit, unit)
                 Pulse_Checker_Prover_Match_Base.match_pass_result,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun label ->
                 fun matcher_f ->
                   fun preamble ->
                     fun pst ->
                       fun ctxt ->
                         fun unsolved ->
                           match unsolved with
                           | [] ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          Pulse_Checker_Prover_Match_Base.mpr_zero
                                            (Pulse_Typing_Env.push_env
                                               pst.Pulse_Checker_Prover_Base.pg
                                               pst.Pulse_Checker_Prover_Base.uvs)
                                            pst.Pulse_Checker_Prover_Base.ss
                                            ctxt unsolved)))
                           | q::qs ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.Match.Comb.fst"
                                                (Prims.of_int (152))
                                                (Prims.of_int (14))
                                                (Prims.of_int (152))
                                                (Prims.of_int (52)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.Match.Comb.fst"
                                                (Prims.of_int (154))
                                                (Prims.of_int (12))
                                                (Prims.of_int (205))
                                                (Prims.of_int (10)))))
                                       (Obj.magic
                                          (match_f_nn label matcher_f
                                             preamble pst ctxt qs))
                                       (fun uu___ ->
                                          (fun mpr ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.Match.Comb.fst"
                                                           (Prims.of_int (155))
                                                           (Prims.of_int (17))
                                                           (Prims.of_int (155))
                                                           (Prims.of_int (38)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.Match.Comb.fst"
                                                           (Prims.of_int (156))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (205))
                                                           (Prims.of_int (10)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___ ->
                                                        {
                                                          Pulse_Checker_Prover_Base.pg
                                                            =
                                                            (pst.Pulse_Checker_Prover_Base.pg);
                                                          Pulse_Checker_Prover_Base.remaining_ctxt
                                                            =
                                                            (pst.Pulse_Checker_Prover_Base.remaining_ctxt);
                                                          Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                            = ();
                                                          Pulse_Checker_Prover_Base.uvs
                                                            =
                                                            (pst.Pulse_Checker_Prover_Base.uvs);
                                                          Pulse_Checker_Prover_Base.ss
                                                            =
                                                            (mpr.Pulse_Checker_Prover_Match_Base.ss');
                                                          Pulse_Checker_Prover_Base.nts
                                                            =
                                                            (pst.Pulse_Checker_Prover_Base.nts);
                                                          Pulse_Checker_Prover_Base.solved
                                                            =
                                                            (pst.Pulse_Checker_Prover_Base.solved);
                                                          Pulse_Checker_Prover_Base.unsolved
                                                            =
                                                            (pst.Pulse_Checker_Prover_Base.unsolved);
                                                          Pulse_Checker_Prover_Base.k
                                                            =
                                                            (pst.Pulse_Checker_Prover_Base.k);
                                                          Pulse_Checker_Prover_Base.goals_inv
                                                            = ();
                                                          Pulse_Checker_Prover_Base.solved_inv
                                                            = ();
                                                          Pulse_Checker_Prover_Base.progress
                                                            =
                                                            (pst.Pulse_Checker_Prover_Base.progress);
                                                          Pulse_Checker_Prover_Base.allow_ambiguous
                                                            =
                                                            (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                                                        }))
                                                  (fun uu___ ->
                                                     (fun pst' ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (66)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (10)))))
                                                             (if
                                                                Pulse_RuntimeUtils.debug_at_level
                                                                  (Pulse_Typing_Env.fstar_env
                                                                    pst.Pulse_Checker_Prover_Base.pg)
                                                                  "prover.match"
                                                              then
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    q))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.strcat
                                                                    uu___
                                                                    " from context"))))
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.strcat
                                                                    "Trying to match goal "
                                                                    uu___))))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    uu___ ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.print
                                                                    uu___))
                                                                    uu___)))
                                                              else
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))))
                                                             (fun uu___ ->
                                                                (fun uu___ ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.try_with
                                                                    (fun
                                                                    uu___1 ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    match_f_1n
                                                                    label
                                                                    matcher_f
                                                                    preamble
                                                                    pst' q
                                                                    mpr.Pulse_Checker_Prover_Match_Base.ctxt1)
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    Pulse_Checker_Prover_Match_Base.Ambig
                                                                    (q1, p,
                                                                    p') ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (12)))))
                                                                    (if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    pst.Pulse_Checker_Prover_Base.pg)
                                                                    "prover.match"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.print
                                                                    "Ambiguity detected... continuing to another goal"))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    q1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "q = "
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.print
                                                                    uu___3))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "p = "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.print
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    p'))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "p' = "
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.print
                                                                    uu___5))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.None)))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    {
                                                                    Pulse_Checker_Prover_Match_Base.ss'
                                                                    =
                                                                    (mpr.Pulse_Checker_Prover_Match_Base.ss');
                                                                    Pulse_Checker_Prover_Match_Base.ctxt_matched
                                                                    =
                                                                    (mpr.Pulse_Checker_Prover_Match_Base.ctxt_matched);
                                                                    Pulse_Checker_Prover_Match_Base.ctxt1
                                                                    =
                                                                    (mpr.Pulse_Checker_Prover_Match_Base.ctxt1);
                                                                    Pulse_Checker_Prover_Match_Base.ctxt_ok
                                                                    = ();
                                                                    Pulse_Checker_Prover_Match_Base.unsolved_matched
                                                                    =
                                                                    (mpr.Pulse_Checker_Prover_Match_Base.unsolved_matched);
                                                                    Pulse_Checker_Prover_Match_Base.unsolved1
                                                                    = (q ::
                                                                    (mpr.Pulse_Checker_Prover_Match_Base.unsolved1));
                                                                    Pulse_Checker_Prover_Match_Base.unsolved_ok
                                                                    = ();
                                                                    Pulse_Checker_Prover_Match_Base.match_ok
                                                                    = ()
                                                                    }
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p,
                                                                    ctxt1,
                                                                    ctxt1_ok,
                                                                    ss', pq))
                                                                    ->
                                                                    {
                                                                    Pulse_Checker_Prover_Match_Base.ss'
                                                                    = ss';
                                                                    Pulse_Checker_Prover_Match_Base.ctxt_matched
                                                                    = (p ::
                                                                    (mpr.Pulse_Checker_Prover_Match_Base.ctxt_matched));
                                                                    Pulse_Checker_Prover_Match_Base.ctxt1
                                                                    = ctxt1;
                                                                    Pulse_Checker_Prover_Match_Base.ctxt_ok
                                                                    = ();
                                                                    Pulse_Checker_Prover_Match_Base.unsolved_matched
                                                                    = (q ::
                                                                    (mpr.Pulse_Checker_Prover_Match_Base.unsolved_matched));
                                                                    Pulse_Checker_Prover_Match_Base.unsolved1
                                                                    =
                                                                    (mpr.Pulse_Checker_Prover_Match_Base.unsolved1);
                                                                    Pulse_Checker_Prover_Match_Base.unsolved_ok
                                                                    = ();
                                                                    Pulse_Checker_Prover_Match_Base.match_ok
                                                                    = ()
                                                                    }))))
                                                                  uu___)))
                                                       uu___))) uu___))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (match_with :
  Prims.string ->
    Pulse_Checker_Prover_Match_Base.matcher_t ->
      Pulse_Checker_Prover_Base.preamble ->
        unit Pulse_Checker_Prover_Base.prover_state ->
          (unit Pulse_Checker_Prover_Base.prover_state, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun label ->
    fun matcher ->
      fun preamble ->
        fun pst ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.Comb.fst"
                     (Prims.of_int (215)) (Prims.of_int (28))
                     (Prims.of_int (215)) (Prims.of_int (110)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.Comb.fst"
                     (Prims.of_int (216)) (Prims.of_int (6))
                     (Prims.of_int (216)) (Prims.of_int (23)))))
            (Obj.magic
               (match_f_nn label matcher preamble pst
                  (FStar_List_Tot_Base.rev
                     pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                  (FStar_List_Tot_Base.rev
                     pst.Pulse_Checker_Prover_Base.unsolved)))
            (fun uu___ ->
               (fun mpr ->
                  Obj.magic
                    (Pulse_Checker_Prover_Match_Base.apply_mpr preamble pst
                       mpr)) uu___)