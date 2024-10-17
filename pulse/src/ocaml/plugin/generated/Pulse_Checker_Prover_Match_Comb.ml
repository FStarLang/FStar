open Prims

let (wrap_matcher :
  Prims.string ->
    Pulse_Checker_Prover_Match_Base.matcher_t ->
      Pulse_Checker_Prover_Base.preamble ->
        unit Pulse_Checker_Prover_Base.prover_state ->
          Pulse_Syntax_Base.slprop ->
            Pulse_Syntax_Base.slprop ->
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
              let uu___ =
                if
                  Pulse_RuntimeUtils.debug_at_level
                    (Pulse_Typing_Env.fstar_env
                       pst.Pulse_Checker_Prover_Base.pg) "prover.match"
                then
                  Obj.magic
                    (Obj.repr
                       (FStarC_Tactics_V1_Builtins.print
                          (Prims.strcat "Trying matcher " label)))
                else
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))) in
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
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun uu___1 ->
                      Obj.magic
                        (FStar_Tactics_V2_Derived.try_with
                           (fun uu___2 ->
                              match () with
                              | () ->
                                  let uu___3 = matcher preamble pst p q in
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
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___5 ->
                                            FStar_Pervasives_Native.Some
                                              uu___4)))
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 match uu___2 with
                                 | Pulse_Checker_Prover_Match_Base.NoMatch s
                                     ->
                                     Obj.magic
                                       (Obj.repr
                                          (let uu___3 =
                                             if
                                               Pulse_RuntimeUtils.debug_at_level
                                                 (Pulse_Typing_Env.fstar_env
                                                    pst.Pulse_Checker_Prover_Base.pg)
                                                 "prover.match"
                                             then
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStarC_Tactics_V1_Builtins.print
                                                       (Prims.strcat
                                                          "NoMatch: " s)))
                                             else
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 -> ()))) in
                                           FStar_Tactics_Effect.tac_bind
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
                                             (Obj.magic uu___3)
                                             (fun uu___4 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___5 ->
                                                     FStar_Pervasives_Native.None))))
                                 | e ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.raise e)))
                                uu___2))) uu___1)
let rec (match_f_1n :
  Prims.string ->
    Pulse_Checker_Prover_Match_Base.matcher_t ->
      Pulse_Checker_Prover_Base.preamble ->
        unit Pulse_Checker_Prover_Base.prover_state ->
          Pulse_Syntax_Base.slprop ->
            Pulse_Syntax_Base.slprop Prims.list ->
              ((Pulse_Syntax_Base.slprop,
                 Pulse_Syntax_Base.slprop Prims.list, unit,
                 Pulse_Checker_Prover_Substs.ss_t, unit)
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
                                    (let uu___ =
                                       if
                                         Pulse_RuntimeUtils.debug_at_level
                                           (Pulse_Typing_Env.fstar_env
                                              pst.Pulse_Checker_Prover_Base.pg)
                                           "prover.match"
                                       then
                                         Obj.magic
                                           (Obj.repr
                                              (let uu___1 =
                                                 let uu___2 =
                                                   Pulse_Typing_Env.range_of_env
                                                     pst.Pulse_Checker_Prover_Base.pg in
                                                 FStar_Tactics_Effect.tac_bind
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
                                                   (Obj.magic uu___2)
                                                   (fun uu___3 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___4 ->
                                                           FStar_Pervasives_Native.Some
                                                             uu___3)) in
                                               FStar_Tactics_Effect.tac_bind
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
                                                 (Obj.magic uu___1)
                                                 (fun uu___2 ->
                                                    (fun uu___2 ->
                                                       let uu___3 =
                                                         let uu___4 =
                                                           let uu___5 =
                                                             let uu___6 =
                                                               Pulse_PP.pp
                                                                 Pulse_PP.printable_term
                                                                 p in
                                                             FStar_Tactics_Effect.tac_bind
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
                                                                  uu___6)
                                                               (fun uu___7 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "p =")
                                                                    uu___7)) in
                                                           FStar_Tactics_Effect.tac_bind
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
                                                                uu___5)
                                                             (fun uu___6 ->
                                                                (fun uu___6
                                                                   ->
                                                                   let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    q) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "q =")
                                                                    uu___10)) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    [uu___9])) in
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
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___6 ::
                                                                    uu___8))))
                                                                  uu___6) in
                                                         FStar_Tactics_Effect.tac_bind
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
                                                           (Obj.magic uu___4)
                                                           (fun uu___5 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___6
                                                                   ->
                                                                   (Pulse_PP.text
                                                                    "Trying to match")
                                                                   :: uu___5)) in
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
                                                            (Obj.magic uu___3)
                                                            (fun uu___4 ->
                                                               (fun uu___4 ->
                                                                  Obj.magic
                                                                    (
                                                                    Pulse_Typing_Env.info_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    uu___2
                                                                    uu___4))
                                                                 uu___4)))
                                                      uu___2)))
                                       else
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 -> ()))) in
                                     FStar_Tactics_Effect.tac_bind
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
                                       (Obj.magic uu___)
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             let uu___2 =
                                               wrap_matcher label matcher
                                                 preamble pst p
                                                 (Pulse_Checker_Prover_Base.op_Array_Access
                                                    pst.Pulse_Checker_Prover_Base.ss
                                                    q) in
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
                                                  (Obj.magic uu___2)
                                                  (fun uu___3 ->
                                                     (fun uu___3 ->
                                                        match uu___3 with
                                                        | FStar_Pervasives_Native.Some
                                                            (Prims.Mkdtuple2
                                                            (ss_extension,
                                                             pq))
                                                            ->
                                                            let uu___4 =
                                                              if
                                                                Prims.op_Negation
                                                                  pst.Pulse_Checker_Prover_Base.allow_ambiguous
                                                              then
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (let uu___5
                                                                    =
                                                                    if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    pst.Pulse_Checker_Prover_Base.pg)
                                                                    "prover.match"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    "Checking for ambiguity"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ()))) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    let uu___7
                                                                    =
                                                                    match_f_1n
                                                                    label
                                                                    matcher
                                                                    preamble
                                                                    pst q ps in
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
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p',
                                                                    uu___9,
                                                                    uu___10,
                                                                    uu___11,
                                                                    uu___12))
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Reflection_TermEq.term_eq
                                                                    p p')
                                                                    then
                                                                    FStar_Tactics_Effect.raise
                                                                    (Pulse_Checker_Prover_Match_Base.Ambig
                                                                    (q, p,
                                                                    p'))
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    -> ())
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ()))))
                                                                    uu___6)))
                                                              else
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ()))) in
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
                                                                    (Prims.of_int (60)))))
                                                                 (Obj.magic
                                                                    uu___4)
                                                                 (fun uu___5
                                                                    ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Checker_Prover_Substs.push_ss
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    ss_extension)) in
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
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun ss'
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    pst.Pulse_Checker_Prover_Base.pg)
                                                                    "prover.match"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    Pulse_Typing_Env.range_of_env
                                                                    pst.Pulse_Checker_Prover_Base.pg in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___10)) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    p in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "p =")
                                                                    uu___14)) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    pst.Pulse_Checker_Prover_Base.ss
                                                                    q) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "q =")
                                                                    uu___17)) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_Checker_Prover_Substs.pp_ss_t
                                                                    ss' in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "ss' =")
                                                                    uu___20)) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                                                    ss' q) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.doc_of_string
                                                                    "ss'.(q) =")
                                                                    uu___23)) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    [uu___22])) in
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
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    uu___19
                                                                    ::
                                                                    uu___21))))
                                                                    uu___19) in
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
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    uu___16
                                                                    ::
                                                                    uu___18))))
                                                                    uu___16) in
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
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    uu___13
                                                                    ::
                                                                    uu___15))))
                                                                    uu___13) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (Pulse_PP.text
                                                                    (Prims.strcat
                                                                    "Matched with "
                                                                    label))
                                                                    ::
                                                                    uu___12)) in
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
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.info_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    uu___9
                                                                    uu___11))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ()))) in
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
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p, ps,
                                                                    (), ss',
                                                                    ()))))))
                                                                    uu___7)))
                                                                    uu___5))
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            let uu___4 =
                                                              match_f_1n
                                                                label matcher
                                                                preamble pst
                                                                q ps in
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
                                                                    uu___4)
                                                                 (fun uu___5
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
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
                                                       uu___3))) uu___1))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let report_ambig :
  'a .
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.slprop ->
        Pulse_Syntax_Base.slprop ->
          Pulse_Syntax_Base.slprop ->
            ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun g ->
    fun q ->
      fun p ->
        fun p' ->
          let uu___ =
            let uu___1 = Pulse_Typing_Env.range_of_env g in
            FStar_Tactics_Effect.tac_bind
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
              (Obj.magic uu___1)
              (fun uu___2 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___3 -> FStar_Pervasives_Native.Some uu___2)) in
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
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 = Pulse_PP.pp Pulse_PP.printable_term q in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.Match.Comb.fst"
                                   (Prims.of_int (131)) (Prims.of_int (13))
                                   (Prims.of_int (131)) (Prims.of_int (19)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.Match.Comb.fst"
                                   (Prims.of_int (131)) (Prims.of_int (6))
                                   (Prims.of_int (131)) (Prims.of_int (19)))))
                          (Obj.magic uu___5)
                          (fun uu___6 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___7 -> Pulse_PP.indent uu___6)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.Match.Comb.fst"
                                 (Prims.of_int (131)) (Prims.of_int (6))
                                 (Prims.of_int (131)) (Prims.of_int (19)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.Match.Comb.fst"
                                 (Prims.of_int (130)) (Prims.of_int (4))
                                 (Prims.of_int (131)) (Prims.of_int (19)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___6 ->
                                FStar_Pprint.op_Hat_Hat
                                  (Pulse_PP.text
                                     "Ambiguous match for resource:") uu___5)) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Pulse.Checker.Prover.Match.Comb.fst"
                               (Prims.of_int (130)) (Prims.of_int (4))
                               (Prims.of_int (131)) (Prims.of_int (19)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Pulse.Checker.Prover.Match.Comb.fst"
                               (Prims.of_int (129)) (Prims.of_int (47))
                               (Prims.of_int (137)) (Prims.of_int (3)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         (fun uu___4 ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      Pulse_PP.pp Pulse_PP.printable_term p in
                                    FStar_Tactics_Effect.tac_bind
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
                                      (Obj.magic uu___9)
                                      (fun uu___10 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___11 ->
                                              Pulse_PP.indent uu___10)) in
                                  FStar_Tactics_Effect.tac_bind
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
                                    (Obj.magic uu___8)
                                    (fun uu___9 ->
                                       (fun uu___9 ->
                                          let uu___10 =
                                            let uu___11 =
                                              let uu___12 =
                                                let uu___13 =
                                                  let uu___14 =
                                                    Pulse_PP.pp
                                                      Pulse_PP.printable_term
                                                      p' in
                                                  FStar_Tactics_Effect.tac_bind
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
                                                    (Obj.magic uu___14)
                                                    (fun uu___15 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___16 ->
                                                            Pulse_PP.indent
                                                              uu___15)) in
                                                FStar_Tactics_Effect.tac_bind
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
                                                  (Obj.magic uu___13)
                                                  (fun uu___14 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___15 ->
                                                          FStar_Pprint.op_Hat_Hat
                                                            uu___14
                                                            (FStar_Pprint.op_Hat_Hat
                                                               FStar_Pprint.hardline
                                                               (Pulse_PP.text
                                                                  "in the context.")))) in
                                              FStar_Tactics_Effect.tac_bind
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
                                                (Obj.magic uu___12)
                                                (fun uu___13 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___14 ->
                                                        FStar_Pprint.op_Hat_Hat
                                                          (Pulse_PP.text
                                                             "and:") uu___13)) in
                                            FStar_Tactics_Effect.tac_bind
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
                                              (Obj.magic uu___11)
                                              (fun uu___12 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___13 ->
                                                      FStar_Pprint.op_Hat_Hat
                                                        FStar_Pprint.hardline
                                                        uu___12)) in
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
                                               (Obj.magic uu___10)
                                               (fun uu___11 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___12 ->
                                                       FStar_Pprint.op_Hat_Hat
                                                         uu___9 uu___11))))
                                         uu___9) in
                                FStar_Tactics_Effect.tac_bind
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
                                  (Obj.magic uu___7)
                                  (fun uu___8 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___9 ->
                                          FStar_Pprint.op_Hat_Hat
                                            (Pulse_PP.text
                                               "It can be matched by both:")
                                            uu___8)) in
                              FStar_Tactics_Effect.tac_bind
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
                                (Obj.magic uu___6)
                                (fun uu___7 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___8 -> [uu___7])) in
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
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> uu___4 :: uu___6))))
                           uu___4) in
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
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             Obj.magic
                               (Pulse_Typing_Env.fail_doc_env true g uu___1
                                  uu___3)) uu___3))) uu___1)
let rec (match_f_nn :
  Prims.string ->
    Pulse_Checker_Prover_Match_Base.matcher_t ->
      Pulse_Checker_Prover_Base.preamble ->
        unit Pulse_Checker_Prover_Base.prover_state ->
          Pulse_Syntax_Base.slprop Prims.list ->
            Pulse_Syntax_Base.slprop Prims.list ->
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
                                    (let uu___ =
                                       match_f_nn label matcher_f preamble
                                         pst ctxt qs in
                                     FStar_Tactics_Effect.tac_bind
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
                                                (Prims.of_int (152))
                                                (Prims.of_int (55))
                                                (Prims.of_int (210))
                                                (Prims.of_int (10)))))
                                       (Obj.magic uu___)
                                       (fun uu___1 ->
                                          (fun mpr ->
                                             let uu___1 =
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
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
                                                           FStar_Pervasives_Native.None;
                                                         Pulse_Checker_Prover_Base.solved
                                                           =
                                                           (pst.Pulse_Checker_Prover_Base.solved);
                                                         Pulse_Checker_Prover_Base.unsolved
                                                           =
                                                           (pst.Pulse_Checker_Prover_Base.unsolved);
                                                         Pulse_Checker_Prover_Base.k
                                                           =
                                                           (FStar_Pervasives.coerce_eq
                                                              ()
                                                              pst.Pulse_Checker_Prover_Base.k);
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
                                                       })) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.Match.Comb.fst"
                                                           (Prims.of_int (154))
                                                           (Prims.of_int (17))
                                                           (Prims.of_int (158))
                                                           (Prims.of_int (27)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.Match.Comb.fst"
                                                           (Prims.of_int (160))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (210))
                                                           (Prims.of_int (10)))))
                                                  (Obj.magic uu___1)
                                                  (fun uu___2 ->
                                                     (fun pst' ->
                                                        let uu___2 =
                                                          if
                                                            Pulse_RuntimeUtils.debug_at_level
                                                              (Pulse_Typing_Env.fstar_env
                                                                 pst.Pulse_Checker_Prover_Base.pg)
                                                              "prover.match"
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (let uu___3
                                                                    =
                                                                    let uu___4
                                                                    =
                                                                    let uu___5
                                                                    =
                                                                    Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    q in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    uu___6
                                                                    " from context")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___4)
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Trying to match goal "
                                                                    uu___5)) in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (66)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (66)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___3)
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___4))
                                                                    uu___4)))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    ()))) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (66)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (10)))))
                                                             (Obj.magic
                                                                uu___2)
                                                             (fun uu___3 ->
                                                                (fun uu___3
                                                                   ->
                                                                   let uu___4
                                                                    =
                                                                    FStar_Tactics_V2_Derived.try_with
                                                                    (fun
                                                                    uu___5 ->
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
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Pulse_Checker_Prover_Match_Base.Ambig
                                                                    (q1, p,
                                                                    p') ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___6
                                                                    =
                                                                    if
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    pst.Pulse_Checker_Prover_Base.pg)
                                                                    "prover.match"
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.print
                                                                    "Ambiguity detected... continuing to another goal" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    q1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    "q = "
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___11))
                                                                    uu___11) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    p in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    "p = "
                                                                    uu___14)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___13))
                                                                    uu___13) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (37)))))
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
                                                                    let uu___14
                                                                    =
                                                                    Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    p' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    "p' = "
                                                                    uu___15)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___14))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (12)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    | 
                                                                    e ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    e)))
                                                                    uu___5) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Match.Comb.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___4)
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
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
                                                                  uu___3)))
                                                       uu___2))) uu___1))))
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
          let uu___ =
            match_f_nn label matcher preamble pst
              pst.Pulse_Checker_Prover_Base.remaining_ctxt
              pst.Pulse_Checker_Prover_Base.unsolved in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.Comb.fst"
                     (Prims.of_int (220)) (Prims.of_int (28))
                     (Prims.of_int (220)) (Prims.of_int (88)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.Match.Comb.fst"
                     (Prims.of_int (221)) (Prims.of_int (6))
                     (Prims.of_int (221)) (Prims.of_int (23)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun mpr ->
                  Obj.magic
                    (Pulse_Checker_Prover_Match_Base.apply_mpr preamble pst
                       mpr)) uu___1)