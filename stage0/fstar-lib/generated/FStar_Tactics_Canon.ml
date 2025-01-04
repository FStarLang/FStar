open Prims
let (step :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      FStar_Tactics_V2_Derived.apply_lemma
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar"; "Tactics"; "Canon"; "Lemmas"; "trans"]))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
               (Prims.of_int (26)) (Prims.of_int (4)) (Prims.of_int (26))
               (Prims.of_int (24)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
               (Prims.of_int (27)) (Prims.of_int (4)) (Prims.of_int (27))
               (Prims.of_int (8))))) (Obj.magic uu___)
      (fun uu___1 -> (fun uu___1 -> Obj.magic (t ())) uu___1)
let (step_lemma :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun lem -> step (fun uu___ -> FStar_Tactics_V2_Derived.apply_lemma lem)
let rec (canon_point :
  FStar_Reflection_V2_Arith.expr ->
    (FStar_Reflection_V2_Arith.expr, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              fun uu___2 ->
                let uu___3 = FStar_Tactics_V2_Derived.trefl () in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                           (Prims.of_int (35)) (Prims.of_int (8))
                           (Prims.of_int (35)) (Prims.of_int (16)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                           (Prims.of_int (33)) (Prims.of_int (20))
                           (Prims.of_int (33)) (Prims.of_int (21)))))
                  (Obj.magic uu___3)
                  (fun uu___4 ->
                     FStar_Tactics_Effect.lift_div_tac (fun uu___5 -> e)))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
               (Prims.of_int (35)) (Prims.of_int (8)) (Prims.of_int (35))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
               (Prims.of_int (37)) (Prims.of_int (4)) (Prims.of_int (153))
               (Prims.of_int (15))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun skip ->
            match e with
            | FStar_Reflection_V2_Arith.Plus
                (FStar_Reflection_V2_Arith.Lit a,
                 FStar_Reflection_V2_Arith.Lit b)
                ->
                let uu___1 =
                  FStarC_Tactics_V2_Builtins.norm [FStar_Pervasives.primops] in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (40)) (Prims.of_int (8))
                              (Prims.of_int (40)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (41)) (Prims.of_int (8))
                              (Prims.of_int (42)) (Prims.of_int (19)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 = FStar_Tactics_V2_Derived.trefl () in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (41))
                                         (Prims.of_int (8))
                                         (Prims.of_int (41))
                                         (Prims.of_int (16)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (42))
                                         (Prims.of_int (8))
                                         (Prims.of_int (42))
                                         (Prims.of_int (19)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        FStar_Reflection_V2_Arith.Lit (a + b)))))
                          uu___2))
            | FStar_Reflection_V2_Arith.Mult
                (FStar_Reflection_V2_Arith.Lit a,
                 FStar_Reflection_V2_Arith.Lit b)
                ->
                let uu___1 =
                  FStarC_Tactics_V2_Builtins.norm
                    [FStar_Pervasives.delta; FStar_Pervasives.primops] in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (45)) (Prims.of_int (8))
                              (Prims.of_int (45)) (Prims.of_int (29)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (46)) (Prims.of_int (8))
                              (Prims.of_int (47)) (Prims.of_int (19)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 = FStar_Tactics_V2_Derived.trefl () in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (46))
                                         (Prims.of_int (8))
                                         (Prims.of_int (46))
                                         (Prims.of_int (16)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (47))
                                         (Prims.of_int (8))
                                         (Prims.of_int (47))
                                         (Prims.of_int (19)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        FStar_Reflection_V2_Arith.Lit (a * b)))))
                          uu___2))
            | FStar_Reflection_V2_Arith.Neg e1 ->
                let uu___1 =
                  step_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Canon";
                             "Lemmas";
                             "neg_minus_one"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (51)) (Prims.of_int (8))
                              (Prims.of_int (51)) (Prims.of_int (35)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (52)) (Prims.of_int (8))
                              (Prims.of_int (52)) (Prims.of_int (39)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           Obj.magic
                             (canon_point
                                (FStar_Reflection_V2_Arith.Mult
                                   ((FStar_Reflection_V2_Arith.Lit
                                       (Prims.of_int (-1))), e1)))) uu___2))
            | FStar_Reflection_V2_Arith.Mult
                (a, FStar_Reflection_V2_Arith.Plus (b, c)) ->
                let uu___1 =
                  step_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar"; "Tactics"; "Canon"; "Lemmas"; "distr"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (56)) (Prims.of_int (8))
                              (Prims.of_int (56)) (Prims.of_int (27)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (57)) (Prims.of_int (8))
                              (Prims.of_int (60)) (Prims.of_int (30)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             step_lemma
                               (FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                     (FStarC_Reflection_V2_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Canon";
                                        "Lemmas";
                                        "cong_plus"]))) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (57))
                                         (Prims.of_int (8))
                                         (Prims.of_int (57))
                                         (Prims.of_int (31)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (57))
                                         (Prims.of_int (32))
                                         (Prims.of_int (60))
                                         (Prims.of_int (30)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun uu___4 ->
                                      let uu___5 =
                                        canon_point
                                          (FStar_Reflection_V2_Arith.Mult
                                             (a, b)) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (58))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (58))
                                                    (Prims.of_int (38)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (58))
                                                    (Prims.of_int (41))
                                                    (Prims.of_int (60))
                                                    (Prims.of_int (30)))))
                                           (Obj.magic uu___5)
                                           (fun uu___6 ->
                                              (fun l ->
                                                 let uu___6 =
                                                   canon_point
                                                     (FStar_Reflection_V2_Arith.Mult
                                                        (a, c)) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (59))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (59))
                                                               (Prims.of_int (38)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (60))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (60))
                                                               (Prims.of_int (30)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_V2_Arith.Plus
                                                                    (l, r))))
                                                           uu___7))) uu___6)))
                                     uu___4))) uu___2))
            | FStar_Reflection_V2_Arith.Mult
                (FStar_Reflection_V2_Arith.Plus (a, b), c) ->
                let uu___1 =
                  step_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar"; "Tactics"; "Canon"; "Lemmas"; "distl"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (63)) (Prims.of_int (8))
                              (Prims.of_int (63)) (Prims.of_int (27)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (64)) (Prims.of_int (8))
                              (Prims.of_int (67)) (Prims.of_int (30)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             step_lemma
                               (FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                     (FStarC_Reflection_V2_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Canon";
                                        "Lemmas";
                                        "cong_plus"]))) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (64))
                                         (Prims.of_int (8))
                                         (Prims.of_int (64))
                                         (Prims.of_int (31)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (64))
                                         (Prims.of_int (32))
                                         (Prims.of_int (67))
                                         (Prims.of_int (30)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun uu___4 ->
                                      let uu___5 =
                                        canon_point
                                          (FStar_Reflection_V2_Arith.Mult
                                             (a, c)) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (65))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (65))
                                                    (Prims.of_int (38)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (65))
                                                    (Prims.of_int (41))
                                                    (Prims.of_int (67))
                                                    (Prims.of_int (30)))))
                                           (Obj.magic uu___5)
                                           (fun uu___6 ->
                                              (fun l ->
                                                 let uu___6 =
                                                   canon_point
                                                     (FStar_Reflection_V2_Arith.Mult
                                                        (b, c)) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (66))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (66))
                                                               (Prims.of_int (38)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (67))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (67))
                                                               (Prims.of_int (30)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_V2_Arith.Plus
                                                                    (l, r))))
                                                           uu___7))) uu___6)))
                                     uu___4))) uu___2))
            | FStar_Reflection_V2_Arith.Mult
                (a, FStar_Reflection_V2_Arith.Mult (b, c)) ->
                let uu___1 =
                  step_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Canon";
                             "Lemmas";
                             "ass_mult_l"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (71)) (Prims.of_int (8))
                              (Prims.of_int (71)) (Prims.of_int (32)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (72)) (Prims.of_int (8))
                              (Prims.of_int (75)) (Prims.of_int (30)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             step_lemma
                               (FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                     (FStarC_Reflection_V2_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Canon";
                                        "Lemmas";
                                        "cong_mult"]))) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (72))
                                         (Prims.of_int (8))
                                         (Prims.of_int (72))
                                         (Prims.of_int (31)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (72))
                                         (Prims.of_int (32))
                                         (Prims.of_int (75))
                                         (Prims.of_int (30)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun uu___4 ->
                                      let uu___5 =
                                        canon_point
                                          (FStar_Reflection_V2_Arith.Mult
                                             (a, b)) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (73))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (73))
                                                    (Prims.of_int (38)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (73))
                                                    (Prims.of_int (41))
                                                    (Prims.of_int (75))
                                                    (Prims.of_int (30)))))
                                           (Obj.magic uu___5)
                                           (fun uu___6 ->
                                              (fun l ->
                                                 let uu___6 = canon_point c in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (74))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (74))
                                                               (Prims.of_int (29)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (75))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (75))
                                                               (Prims.of_int (30)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_V2_Arith.Mult
                                                                    (l, r))))
                                                           uu___7))) uu___6)))
                                     uu___4))) uu___2))
            | FStar_Reflection_V2_Arith.Plus
                (a, FStar_Reflection_V2_Arith.Plus (b, c)) ->
                let uu___1 =
                  step_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Canon";
                             "Lemmas";
                             "ass_plus_l"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (78)) (Prims.of_int (8))
                              (Prims.of_int (78)) (Prims.of_int (32)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (79)) (Prims.of_int (8))
                              (Prims.of_int (82)) (Prims.of_int (30)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             step_lemma
                               (FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                     (FStarC_Reflection_V2_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Canon";
                                        "Lemmas";
                                        "cong_plus"]))) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (79))
                                         (Prims.of_int (8))
                                         (Prims.of_int (79))
                                         (Prims.of_int (31)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (79))
                                         (Prims.of_int (32))
                                         (Prims.of_int (82))
                                         (Prims.of_int (30)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun uu___4 ->
                                      let uu___5 =
                                        canon_point
                                          (FStar_Reflection_V2_Arith.Plus
                                             (a, b)) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (80))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (80))
                                                    (Prims.of_int (38)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (80))
                                                    (Prims.of_int (41))
                                                    (Prims.of_int (82))
                                                    (Prims.of_int (30)))))
                                           (Obj.magic uu___5)
                                           (fun uu___6 ->
                                              (fun l ->
                                                 let uu___6 = canon_point c in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (81))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (81))
                                                               (Prims.of_int (29)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (82))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (82))
                                                               (Prims.of_int (30)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_V2_Arith.Plus
                                                                    (l, r))))
                                                           uu___7))) uu___6)))
                                     uu___4))) uu___2))
            | FStar_Reflection_V2_Arith.Plus
                (FStar_Reflection_V2_Arith.Plus (a, b), c) ->
                if
                  FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr b c)
                then
                  let uu___1 =
                    step_lemma
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "Canon";
                               "Lemmas";
                               "sw_plus"]))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                                (Prims.of_int (87)) (Prims.of_int (12))
                                (Prims.of_int (87)) (Prims.of_int (33)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                                (Prims.of_int (88)) (Prims.of_int (12))
                                (Prims.of_int (91)) (Prims.of_int (20)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun uu___2 ->
                             let uu___3 =
                               FStar_Tactics_V2_Derived.apply_lemma
                                 (FStarC_Reflection_V2_Builtins.pack_ln
                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                       (FStarC_Reflection_V2_Builtins.pack_fv
                                          ["FStar";
                                          "Tactics";
                                          "Canon";
                                          "Lemmas";
                                          "cong_plus"]))) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (88))
                                           (Prims.of_int (12))
                                           (Prims.of_int (88))
                                           (Prims.of_int (36)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (88))
                                           (Prims.of_int (37))
                                           (Prims.of_int (91))
                                           (Prims.of_int (20)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        let uu___5 =
                                          canon_point
                                            (FStar_Reflection_V2_Arith.Plus
                                               (a, c)) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.Canon.fst"
                                                      (Prims.of_int (89))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (89))
                                                      (Prims.of_int (42)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.Canon.fst"
                                                      (Prims.of_int (90))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (91))
                                                      (Prims.of_int (20)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun l ->
                                                   let uu___6 =
                                                     FStar_Tactics_V2_Derived.trefl
                                                       () in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.Canon.fst"
                                                                 (Prims.of_int (90))
                                                                 (Prims.of_int (12))
                                                                 (Prims.of_int (90))
                                                                 (Prims.of_int (19)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.Canon.fst"
                                                                 (Prims.of_int (91))
                                                                 (Prims.of_int (12))
                                                                 (Prims.of_int (91))
                                                                 (Prims.of_int (20)))))
                                                        (Obj.magic uu___6)
                                                        (fun uu___7 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___8 ->
                                                                FStar_Reflection_V2_Arith.Plus
                                                                  (l, b)))))
                                                  uu___6))) uu___4))) uu___2))
                else Obj.magic (skip ())
            | FStar_Reflection_V2_Arith.Mult
                (FStar_Reflection_V2_Arith.Mult (a, b), c) ->
                if
                  FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr b c)
                then
                  let uu___1 =
                    step_lemma
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "Canon";
                               "Lemmas";
                               "sw_mult"]))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                                (Prims.of_int (98)) (Prims.of_int (12))
                                (Prims.of_int (98)) (Prims.of_int (33)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                                (Prims.of_int (99)) (Prims.of_int (12))
                                (Prims.of_int (102)) (Prims.of_int (20)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun uu___2 ->
                             let uu___3 =
                               FStar_Tactics_V2_Derived.apply_lemma
                                 (FStarC_Reflection_V2_Builtins.pack_ln
                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                       (FStarC_Reflection_V2_Builtins.pack_fv
                                          ["FStar";
                                          "Tactics";
                                          "Canon";
                                          "Lemmas";
                                          "cong_mult"]))) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (99))
                                           (Prims.of_int (12))
                                           (Prims.of_int (99))
                                           (Prims.of_int (36)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Canon.fst"
                                           (Prims.of_int (99))
                                           (Prims.of_int (37))
                                           (Prims.of_int (102))
                                           (Prims.of_int (20)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        let uu___5 =
                                          canon_point
                                            (FStar_Reflection_V2_Arith.Mult
                                               (a, c)) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.Canon.fst"
                                                      (Prims.of_int (100))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (100))
                                                      (Prims.of_int (42)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.Canon.fst"
                                                      (Prims.of_int (101))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (102))
                                                      (Prims.of_int (20)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun l ->
                                                   let uu___6 =
                                                     FStar_Tactics_V2_Derived.trefl
                                                       () in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.Canon.fst"
                                                                 (Prims.of_int (101))
                                                                 (Prims.of_int (12))
                                                                 (Prims.of_int (101))
                                                                 (Prims.of_int (20)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.Canon.fst"
                                                                 (Prims.of_int (102))
                                                                 (Prims.of_int (12))
                                                                 (Prims.of_int (102))
                                                                 (Prims.of_int (20)))))
                                                        (Obj.magic uu___6)
                                                        (fun uu___7 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___8 ->
                                                                FStar_Reflection_V2_Arith.Mult
                                                                  (l, b)))))
                                                  uu___6))) uu___4))) uu___2))
                else Obj.magic (skip ())
            | FStar_Reflection_V2_Arith.Plus
                (a, FStar_Reflection_V2_Arith.Lit uu___1) when
                uu___1 = Prims.int_zero ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Canon";
                             "Lemmas";
                             "x_plus_zero"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (107)) (Prims.of_int (8))
                              (Prims.of_int (107)) (Prims.of_int (34)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (106)) (Prims.of_int (11))
                              (Prims.of_int (106)) (Prims.of_int (12)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> a)))
            | FStar_Reflection_V2_Arith.Plus
                (FStar_Reflection_V2_Arith.Lit uu___1, b) when
                uu___1 = Prims.int_zero ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Canon";
                             "Lemmas";
                             "zero_plus_x"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (111)) (Prims.of_int (8))
                              (Prims.of_int (111)) (Prims.of_int (34)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (110)) (Prims.of_int (19))
                              (Prims.of_int (110)) (Prims.of_int (20)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> b)))
            | FStar_Reflection_V2_Arith.Plus (a, b) ->
                if
                  FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr a b)
                then
                  let uu___1 =
                    FStar_Tactics_V2_Derived.apply_lemma
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "Canon";
                               "Lemmas";
                               "comm_plus"]))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                                (Prims.of_int (116)) (Prims.of_int (14))
                                (Prims.of_int (116)) (Prims.of_int (38)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                                (Prims.of_int (116)) (Prims.of_int (40))
                                (Prims.of_int (116)) (Prims.of_int (48)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 ->
                               FStar_Reflection_V2_Arith.Plus (b, a))))
                else Obj.magic (skip ())
            | FStar_Reflection_V2_Arith.Mult
                (FStar_Reflection_V2_Arith.Lit uu___1, uu___2) when
                uu___1 = Prims.int_zero ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Canon";
                             "Lemmas";
                             "zero_mult_x"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (120)) (Prims.of_int (8))
                              (Prims.of_int (120)) (Prims.of_int (34)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (121)) (Prims.of_int (8))
                              (Prims.of_int (121)) (Prims.of_int (13)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___5 ->
                             FStar_Reflection_V2_Arith.Lit Prims.int_zero)))
            | FStar_Reflection_V2_Arith.Mult
                (uu___1, FStar_Reflection_V2_Arith.Lit uu___2) when
                uu___2 = Prims.int_zero ->
                let uu___3 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Canon";
                             "Lemmas";
                             "x_mult_zero"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (124)) (Prims.of_int (8))
                              (Prims.of_int (124)) (Prims.of_int (34)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (125)) (Prims.of_int (8))
                              (Prims.of_int (125)) (Prims.of_int (13)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___5 ->
                             FStar_Reflection_V2_Arith.Lit Prims.int_zero)))
            | FStar_Reflection_V2_Arith.Mult
                (FStar_Reflection_V2_Arith.Lit uu___1, r) when
                uu___1 = Prims.int_one ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Canon";
                             "Lemmas";
                             "one_mult_x"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (128)) (Prims.of_int (8))
                              (Prims.of_int (128)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (127)) (Prims.of_int (19))
                              (Prims.of_int (127)) (Prims.of_int (20)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> r)))
            | FStar_Reflection_V2_Arith.Mult
                (l, FStar_Reflection_V2_Arith.Lit uu___1) when
                uu___1 = Prims.int_one ->
                let uu___2 =
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Canon";
                             "Lemmas";
                             "x_mult_one"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (132)) (Prims.of_int (8))
                              (Prims.of_int (132)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (131)) (Prims.of_int (11))
                              (Prims.of_int (131)) (Prims.of_int (12)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> l)))
            | FStar_Reflection_V2_Arith.Mult (a, b) ->
                if
                  FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr a b)
                then
                  let uu___1 =
                    FStar_Tactics_V2_Derived.apply_lemma
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "Canon";
                               "Lemmas";
                               "comm_mult"]))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                                (Prims.of_int (137)) (Prims.of_int (14))
                                (Prims.of_int (137)) (Prims.of_int (38)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                                (Prims.of_int (137)) (Prims.of_int (40))
                                (Prims.of_int (137)) (Prims.of_int (48)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 ->
                               FStar_Reflection_V2_Arith.Mult (b, a))))
                else Obj.magic (skip ())
            | FStar_Reflection_V2_Arith.Minus (a, b) ->
                let uu___1 =
                  step_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Canon";
                             "Lemmas";
                             "minus_is_plus"]))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (142)) (Prims.of_int (8))
                              (Prims.of_int (142)) (Prims.of_int (35)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                              (Prims.of_int (143)) (Prims.of_int (8))
                              (Prims.of_int (150)) (Prims.of_int (30)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             step_lemma
                               (FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                     (FStarC_Reflection_V2_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Canon";
                                        "Lemmas";
                                        "cong_plus"]))) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (143))
                                         (Prims.of_int (8))
                                         (Prims.of_int (143))
                                         (Prims.of_int (31)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Canon.fst"
                                         (Prims.of_int (144))
                                         (Prims.of_int (8))
                                         (Prims.of_int (150))
                                         (Prims.of_int (30)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun uu___4 ->
                                      let uu___5 =
                                        FStar_Tactics_V2_Derived.trefl () in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (144))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (144))
                                                    (Prims.of_int (16)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (144))
                                                    (Prims.of_int (17))
                                                    (Prims.of_int (150))
                                                    (Prims.of_int (30)))))
                                           (Obj.magic uu___5)
                                           (fun uu___6 ->
                                              (fun uu___6 ->
                                                 let uu___7 =
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___8 ->
                                                           match b with
                                                           | FStar_Reflection_V2_Arith.Lit
                                                               n ->
                                                               FStar_Reflection_V2_Arith.Lit
                                                                 (- n)
                                                           | uu___9 ->
                                                               FStar_Reflection_V2_Arith.Neg
                                                                 b)) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (145))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (145))
                                                               (Prims.of_int (64)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Canon.fst"
                                                               (Prims.of_int (145))
                                                               (Prims.of_int (67))
                                                               (Prims.of_int (150))
                                                               (Prims.of_int (30)))))
                                                      (Obj.magic uu___7)
                                                      (fun uu___8 ->
                                                         (fun negb ->
                                                            let uu___8 =
                                                              canon_point
                                                                negb in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (32)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Canon.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (30)))))
                                                                 (Obj.magic
                                                                    uu___8)
                                                                 (fun uu___9
                                                                    ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (canon_point
                                                                    (FStar_Reflection_V2_Arith.Plus
                                                                    (a, r))))
                                                                    uu___9)))
                                                           uu___8))) uu___6)))
                                     uu___4))) uu___2))
            | uu___1 -> Obj.magic (skip ())) uu___1)
let (canon_point_entry : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V2_Builtins.norm [FStar_Pervasives.primops] in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
               (Prims.of_int (167)) (Prims.of_int (4)) (Prims.of_int (167))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
               (Prims.of_int (167)) (Prims.of_int (19)) (Prims.of_int (176))
               (Prims.of_int (48))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 = FStar_Tactics_V2_Derived.cur_goal () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (168)) (Prims.of_int (12))
                          (Prims.of_int (168)) (Prims.of_int (23)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (169)) (Prims.of_int (4))
                          (Prims.of_int (176)) (Prims.of_int (48)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun g ->
                       let uu___4 =
                         FStar_Reflection_V2_Formula.term_as_formula g in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Canon.fst"
                                     (Prims.of_int (169)) (Prims.of_int (10))
                                     (Prims.of_int (169)) (Prims.of_int (27)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Canon.fst"
                                     (Prims.of_int (169)) (Prims.of_int (4))
                                     (Prims.of_int (176)) (Prims.of_int (48)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  match uu___5 with
                                  | FStar_Reflection_V2_Formula.Comp
                                      (FStar_Reflection_V2_Formula.Eq uu___6,
                                       l, r)
                                      ->
                                      let uu___7 =
                                        FStar_Reflection_V2_Arith.run_tm
                                          (FStar_Reflection_V2_Arith.is_arith_expr
                                             l) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (171))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (171))
                                                    (Prims.of_int (44)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (171))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (173))
                                                    (Prims.of_int (27)))))
                                           (Obj.magic uu___7)
                                           (fun uu___8 ->
                                              (fun uu___8 ->
                                                 match uu___8 with
                                                 | FStar_Pervasives.Inr e ->
                                                     let uu___9 =
                                                       canon_point e in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Canon.fst"
                                                                   (Prims.of_int (172))
                                                                   (Prims.of_int (29))
                                                                   (Prims.of_int (172))
                                                                   (Prims.of_int (42)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Canon.fst"
                                                                   (Prims.of_int (172))
                                                                   (Prims.of_int (46))
                                                                   (Prims.of_int (172))
                                                                   (Prims.of_int (48)))))
                                                          (Obj.magic uu___9)
                                                          (fun _e ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___10
                                                                  -> ())))
                                                 | FStar_Pervasives.Inl
                                                     uu___9 ->
                                                     Obj.magic
                                                       (FStar_Tactics_V2_Derived.trefl
                                                          ())) uu___8))
                                  | uu___6 ->
                                      let uu___7 =
                                        let uu___8 =
                                          FStarC_Tactics_V2_Builtins.term_to_string
                                            g in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Canon.fst"
                                                   (Prims.of_int (176))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (176))
                                                   (Prims.of_int (47)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Prims.fst"
                                                   (Prims.of_int (611))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (611))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic uu___8)
                                          (fun uu___9 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___10 ->
                                                  Prims.strcat "impossible: "
                                                    uu___9)) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (176))
                                                    (Prims.of_int (13))
                                                    (Prims.of_int (176))
                                                    (Prims.of_int (48)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (176))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (176))
                                                    (Prims.of_int (48)))))
                                           (Obj.magic uu___7)
                                           (fun uu___8 ->
                                              FStar_Tactics_V2_Derived.fail
                                                uu___8))) uu___5))) uu___4)))
           uu___2)
let (canon : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStar_Tactics_V2_Derived.pointwise canon_point_entry
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.Canon.canon"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Canon.canon (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 canon)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)