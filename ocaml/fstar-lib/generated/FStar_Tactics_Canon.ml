open Prims
let (step :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
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
               (Prims.of_int (8)))))
      (Obj.magic
         (FStar_Tactics_V2_Derived.apply_lemma
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Canon"; "Lemmas"; "trans"])))))
      (fun uu___ -> (fun uu___ -> Obj.magic (t ())) uu___)
let (step_lemma :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun lem -> step (fun uu___ -> FStar_Tactics_V2_Derived.apply_lemma lem)
let rec (canon_point :
  FStar_Reflection_V2_Arith.expr ->
    (FStar_Reflection_V2_Arith.expr, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
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
               (Prims.of_int (15)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            fun uu___1 ->
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
                (Obj.magic (FStar_Tactics_V2_Derived.trefl ()))
                (fun uu___2 ->
                   FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> e))))
      (fun uu___ ->
         (fun skip ->
            match e with
            | FStar_Reflection_V2_Arith.Plus
                (FStar_Reflection_V2_Arith.Lit a,
                 FStar_Reflection_V2_Arith.Lit b)
                ->
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
                     (Obj.magic
                        (FStar_Tactics_V2_Builtins.norm
                           [FStar_Pervasives.primops]))
                     (fun uu___ ->
                        (fun uu___ ->
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
                                (Obj.magic
                                   (FStar_Tactics_V2_Derived.trefl ()))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        FStar_Reflection_V2_Arith.Lit (a + b)))))
                          uu___))
            | FStar_Reflection_V2_Arith.Mult
                (FStar_Reflection_V2_Arith.Lit a,
                 FStar_Reflection_V2_Arith.Lit b)
                ->
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
                     (Obj.magic
                        (FStar_Tactics_V2_Builtins.norm
                           [FStar_Pervasives.delta; FStar_Pervasives.primops]))
                     (fun uu___ ->
                        (fun uu___ ->
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
                                (Obj.magic
                                   (FStar_Tactics_V2_Derived.trefl ()))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        FStar_Reflection_V2_Arith.Lit (a * b)))))
                          uu___))
            | FStar_Reflection_V2_Arith.Neg e1 ->
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
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "neg_minus_one"])))))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (canon_point
                                (FStar_Reflection_V2_Arith.Mult
                                   ((FStar_Reflection_V2_Arith.Lit
                                       (Prims.of_int (-1))), e1)))) uu___))
            | FStar_Reflection_V2_Arith.Mult
                (a, FStar_Reflection_V2_Arith.Plus (b, c)) ->
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
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "distr"])))))
                     (fun uu___ ->
                        (fun uu___ ->
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
                                (Obj.magic
                                   (step_lemma
                                      (FStar_Reflection_V2_Builtins.pack_ln
                                         (FStar_Reflection_V2_Data.Tv_FVar
                                            (FStar_Reflection_V2_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "Lemmas";
                                               "cong_plus"])))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
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
                                           (Obj.magic
                                              (canon_point
                                                 (FStar_Reflection_V2_Arith.Mult
                                                    (a, b))))
                                           (fun uu___2 ->
                                              (fun l ->
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
                                                      (Obj.magic
                                                         (canon_point
                                                            (FStar_Reflection_V2_Arith.Mult
                                                               (a, c))))
                                                      (fun uu___2 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_V2_Arith.Plus
                                                                    (l, r))))
                                                           uu___2))) uu___2)))
                                     uu___1))) uu___))
            | FStar_Reflection_V2_Arith.Mult
                (FStar_Reflection_V2_Arith.Plus (a, b), c) ->
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
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "distl"])))))
                     (fun uu___ ->
                        (fun uu___ ->
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
                                (Obj.magic
                                   (step_lemma
                                      (FStar_Reflection_V2_Builtins.pack_ln
                                         (FStar_Reflection_V2_Data.Tv_FVar
                                            (FStar_Reflection_V2_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "Lemmas";
                                               "cong_plus"])))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
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
                                           (Obj.magic
                                              (canon_point
                                                 (FStar_Reflection_V2_Arith.Mult
                                                    (a, c))))
                                           (fun uu___2 ->
                                              (fun l ->
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
                                                      (Obj.magic
                                                         (canon_point
                                                            (FStar_Reflection_V2_Arith.Mult
                                                               (b, c))))
                                                      (fun uu___2 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_V2_Arith.Plus
                                                                    (l, r))))
                                                           uu___2))) uu___2)))
                                     uu___1))) uu___))
            | FStar_Reflection_V2_Arith.Mult
                (a, FStar_Reflection_V2_Arith.Mult (b, c)) ->
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
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "ass_mult_l"])))))
                     (fun uu___ ->
                        (fun uu___ ->
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
                                (Obj.magic
                                   (step_lemma
                                      (FStar_Reflection_V2_Builtins.pack_ln
                                         (FStar_Reflection_V2_Data.Tv_FVar
                                            (FStar_Reflection_V2_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "Lemmas";
                                               "cong_mult"])))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
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
                                           (Obj.magic
                                              (canon_point
                                                 (FStar_Reflection_V2_Arith.Mult
                                                    (a, b))))
                                           (fun uu___2 ->
                                              (fun l ->
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
                                                      (Obj.magic
                                                         (canon_point c))
                                                      (fun uu___2 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_V2_Arith.Mult
                                                                    (l, r))))
                                                           uu___2))) uu___2)))
                                     uu___1))) uu___))
            | FStar_Reflection_V2_Arith.Plus
                (a, FStar_Reflection_V2_Arith.Plus (b, c)) ->
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
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "ass_plus_l"])))))
                     (fun uu___ ->
                        (fun uu___ ->
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
                                (Obj.magic
                                   (step_lemma
                                      (FStar_Reflection_V2_Builtins.pack_ln
                                         (FStar_Reflection_V2_Data.Tv_FVar
                                            (FStar_Reflection_V2_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "Lemmas";
                                               "cong_plus"])))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
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
                                           (Obj.magic
                                              (canon_point
                                                 (FStar_Reflection_V2_Arith.Plus
                                                    (a, b))))
                                           (fun uu___2 ->
                                              (fun l ->
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
                                                      (Obj.magic
                                                         (canon_point c))
                                                      (fun uu___2 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_V2_Arith.Plus
                                                                    (l, r))))
                                                           uu___2))) uu___2)))
                                     uu___1))) uu___))
            | FStar_Reflection_V2_Arith.Plus
                (FStar_Reflection_V2_Arith.Plus (a, b), c) ->
                if
                  FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr b c)
                then
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
                       (Obj.magic
                          (step_lemma
                             (FStar_Reflection_V2_Builtins.pack_ln
                                (FStar_Reflection_V2_Data.Tv_FVar
                                   (FStar_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "Canon";
                                      "Lemmas";
                                      "sw_plus"])))))
                       (fun uu___ ->
                          (fun uu___ ->
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
                                  (Obj.magic
                                     (FStar_Tactics_V2_Derived.apply_lemma
                                        (FStar_Reflection_V2_Builtins.pack_ln
                                           (FStar_Reflection_V2_Data.Tv_FVar
                                              (FStar_Reflection_V2_Builtins.pack_fv
                                                 ["FStar";
                                                 "Tactics";
                                                 "Canon";
                                                 "Lemmas";
                                                 "cong_plus"])))))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
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
                                             (Obj.magic
                                                (canon_point
                                                   (FStar_Reflection_V2_Arith.Plus
                                                      (a, c))))
                                             (fun uu___2 ->
                                                (fun l ->
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
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Derived.trefl
                                                              ()))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                FStar_Reflection_V2_Arith.Plus
                                                                  (l, b)))))
                                                  uu___2))) uu___1))) uu___))
                else Obj.magic (skip ())
            | FStar_Reflection_V2_Arith.Mult
                (FStar_Reflection_V2_Arith.Mult (a, b), c) ->
                if
                  FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr b c)
                then
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
                       (Obj.magic
                          (step_lemma
                             (FStar_Reflection_V2_Builtins.pack_ln
                                (FStar_Reflection_V2_Data.Tv_FVar
                                   (FStar_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "Canon";
                                      "Lemmas";
                                      "sw_mult"])))))
                       (fun uu___ ->
                          (fun uu___ ->
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
                                  (Obj.magic
                                     (FStar_Tactics_V2_Derived.apply_lemma
                                        (FStar_Reflection_V2_Builtins.pack_ln
                                           (FStar_Reflection_V2_Data.Tv_FVar
                                              (FStar_Reflection_V2_Builtins.pack_fv
                                                 ["FStar";
                                                 "Tactics";
                                                 "Canon";
                                                 "Lemmas";
                                                 "cong_mult"])))))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
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
                                             (Obj.magic
                                                (canon_point
                                                   (FStar_Reflection_V2_Arith.Mult
                                                      (a, c))))
                                             (fun uu___2 ->
                                                (fun l ->
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
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Derived.trefl
                                                              ()))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                FStar_Reflection_V2_Arith.Mult
                                                                  (l, b)))))
                                                  uu___2))) uu___1))) uu___))
                else Obj.magic (skip ())
            | FStar_Reflection_V2_Arith.Plus
                (a, FStar_Reflection_V2_Arith.Lit uu___) when
                uu___ = Prims.int_zero ->
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
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "x_plus_zero"])))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> a)))
            | FStar_Reflection_V2_Arith.Plus
                (FStar_Reflection_V2_Arith.Lit uu___, b) when
                uu___ = Prims.int_zero ->
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
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "zero_plus_x"])))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> b)))
            | FStar_Reflection_V2_Arith.Plus (a, b) ->
                if
                  FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr a b)
                then
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
                       (Obj.magic
                          (FStar_Tactics_V2_Derived.apply_lemma
                             (FStar_Reflection_V2_Builtins.pack_ln
                                (FStar_Reflection_V2_Data.Tv_FVar
                                   (FStar_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "Canon";
                                      "Lemmas";
                                      "comm_plus"])))))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Reflection_V2_Arith.Plus (b, a))))
                else Obj.magic (skip ())
            | FStar_Reflection_V2_Arith.Mult
                (FStar_Reflection_V2_Arith.Lit uu___, uu___1) when
                uu___ = Prims.int_zero ->
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
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "zero_mult_x"])))))
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 ->
                             FStar_Reflection_V2_Arith.Lit Prims.int_zero)))
            | FStar_Reflection_V2_Arith.Mult
                (uu___, FStar_Reflection_V2_Arith.Lit uu___1) when
                uu___1 = Prims.int_zero ->
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
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "x_mult_zero"])))))
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 ->
                             FStar_Reflection_V2_Arith.Lit Prims.int_zero)))
            | FStar_Reflection_V2_Arith.Mult
                (FStar_Reflection_V2_Arith.Lit uu___, r) when
                uu___ = Prims.int_one ->
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
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "one_mult_x"])))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> r)))
            | FStar_Reflection_V2_Arith.Mult
                (l, FStar_Reflection_V2_Arith.Lit uu___) when
                uu___ = Prims.int_one ->
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
                     (Obj.magic
                        (FStar_Tactics_V2_Derived.apply_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "x_mult_one"])))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> l)))
            | FStar_Reflection_V2_Arith.Mult (a, b) ->
                if
                  FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr a b)
                then
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
                       (Obj.magic
                          (FStar_Tactics_V2_Derived.apply_lemma
                             (FStar_Reflection_V2_Builtins.pack_ln
                                (FStar_Reflection_V2_Data.Tv_FVar
                                   (FStar_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "Canon";
                                      "Lemmas";
                                      "comm_mult"])))))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Reflection_V2_Arith.Mult (b, a))))
                else Obj.magic (skip ())
            | FStar_Reflection_V2_Arith.Minus (a, b) ->
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
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "Lemmas";
                                    "minus_is_plus"])))))
                     (fun uu___ ->
                        (fun uu___ ->
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
                                (Obj.magic
                                   (step_lemma
                                      (FStar_Reflection_V2_Builtins.pack_ln
                                         (FStar_Reflection_V2_Data.Tv_FVar
                                            (FStar_Reflection_V2_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "Lemmas";
                                               "cong_plus"])))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
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
                                           (Obj.magic
                                              (FStar_Tactics_V2_Derived.trefl
                                                 ()))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
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
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            match b with
                                                            | FStar_Reflection_V2_Arith.Lit
                                                                n ->
                                                                FStar_Reflection_V2_Arith.Lit
                                                                  (- n)
                                                            | uu___4 ->
                                                                FStar_Reflection_V2_Arith.Neg
                                                                  b))
                                                      (fun uu___3 ->
                                                         (fun negb ->
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
                                                                    (
                                                                    canon_point
                                                                    negb))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (canon_point
                                                                    (FStar_Reflection_V2_Arith.Plus
                                                                    (a, r))))
                                                                    uu___3)))
                                                           uu___3))) uu___2)))
                                     uu___1))) uu___))
            | uu___ -> Obj.magic (skip ())) uu___)
let (canon_point_entry : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
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
               (Prims.of_int (48)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.norm [FStar_Pervasives.primops]))
      (fun uu___1 ->
         (fun uu___1 ->
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
                 (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
                 (fun uu___2 ->
                    (fun g ->
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
                            (Obj.magic
                               (FStar_Reflection_V2_Formula.term_as_formula g))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  match uu___2 with
                                  | FStar_Reflection_V2_Formula.Comp
                                      (FStar_Reflection_V2_Formula.Eq uu___3,
                                       l, r)
                                      ->
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
                                           (Obj.magic
                                              (FStar_Reflection_V2_Arith.run_tm
                                                 (FStar_Reflection_V2_Arith.is_arith_expr
                                                    l)))
                                           (fun uu___4 ->
                                              (fun uu___4 ->
                                                 match uu___4 with
                                                 | FStar_Pervasives.Inr e ->
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
                                                          (Obj.magic
                                                             (canon_point e))
                                                          (fun _e ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___5 ->
                                                                  ())))
                                                 | FStar_Pervasives.Inl
                                                     uu___5 ->
                                                     Obj.magic
                                                       (FStar_Tactics_V2_Derived.trefl
                                                          ())) uu___4))
                                  | uu___3 ->
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
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
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
                                                          "prims.fst"
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (31)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                       g))
                                                 (fun uu___4 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___5 ->
                                                         Prims.strcat
                                                           "impossible: "
                                                           uu___4))))
                                           (fun uu___4 ->
                                              FStar_Tactics_V2_Derived.fail
                                                uu___4))) uu___2))) uu___2)))
           uu___1)
let (canon : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStar_Tactics_V2_Derived.pointwise canon_point_entry
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.Canon.canon"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Canon.canon (plugin)"
               (FStar_Tactics_Native.from_tactic_1 canon)
               FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
               psc ncb us args)