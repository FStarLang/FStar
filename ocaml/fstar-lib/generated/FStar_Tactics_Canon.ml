open Prims
let (step :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Canon.fst" (Prims.of_int (126))
         (Prims.of_int (4)) (Prims.of_int (126)) (Prims.of_int (24)))
      (Prims.mk_range "FStar.Tactics.Canon.fst" (Prims.of_int (127))
         (Prims.of_int (4)) (Prims.of_int (127)) (Prims.of_int (8)))
      (Obj.magic
         (FStar_Tactics_Derived.apply_lemma
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Canon"; "trans"])))))
      (fun uu___ -> (fun uu___ -> Obj.magic (t ())) uu___)
let (step_lemma :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun lem -> step (fun uu___ -> FStar_Tactics_Derived.apply_lemma lem)
let rec (canon_point :
  FStar_Reflection_Arith.expr ->
    (FStar_Reflection_Arith.expr, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Canon.fst" (Prims.of_int (136))
         (Prims.of_int (8)) (Prims.of_int (136)) (Prims.of_int (19)))
      (Prims.mk_range "FStar.Tactics.Canon.fst" (Prims.of_int (138))
         (Prims.of_int (4)) (Prims.of_int (250)) (Prims.of_int (15)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            fun uu___1 ->
              FStar_Tactics_Effect.tac_bind
                (Prims.mk_range "FStar.Tactics.Canon.fst"
                   (Prims.of_int (136)) (Prims.of_int (8))
                   (Prims.of_int (136)) (Prims.of_int (16)))
                (Prims.mk_range "FStar.Tactics.Canon.fst"
                   (Prims.of_int (134)) (Prims.of_int (28))
                   (Prims.of_int (134)) (Prims.of_int (29)))
                (Obj.magic (FStar_Tactics_Derived.trefl ()))
                (fun uu___2 ->
                   FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> e))))
      (fun uu___ ->
         (fun skip ->
            match e with
            | FStar_Reflection_Arith.Plus
                (FStar_Reflection_Arith.Lit a, FStar_Reflection_Arith.Lit b)
                ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (141)) (Prims.of_int (8))
                        (Prims.of_int (141)) (Prims.of_int (22)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (142)) (Prims.of_int (8))
                        (Prims.of_int (143)) (Prims.of_int (19)))
                     (Obj.magic
                        (FStar_Tactics_Builtins.norm
                           [FStar_Pervasives.primops]))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (142)) (Prims.of_int (8))
                                   (Prims.of_int (142)) (Prims.of_int (16)))
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (143)) (Prims.of_int (8))
                                   (Prims.of_int (143)) (Prims.of_int (19)))
                                (Obj.magic (FStar_Tactics_Derived.trefl ()))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        FStar_Reflection_Arith.Lit (a + b)))))
                          uu___))
            | FStar_Reflection_Arith.Mult
                (FStar_Reflection_Arith.Lit a, FStar_Reflection_Arith.Lit b)
                ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (146)) (Prims.of_int (8))
                        (Prims.of_int (146)) (Prims.of_int (29)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (147)) (Prims.of_int (8))
                        (Prims.of_int (148)) (Prims.of_int (19)))
                     (Obj.magic
                        (FStar_Tactics_Builtins.norm
                           [FStar_Pervasives.delta; FStar_Pervasives.primops]))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (147)) (Prims.of_int (8))
                                   (Prims.of_int (147)) (Prims.of_int (16)))
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (148)) (Prims.of_int (8))
                                   (Prims.of_int (148)) (Prims.of_int (19)))
                                (Obj.magic (FStar_Tactics_Derived.trefl ()))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        FStar_Reflection_Arith.Lit (a * b)))))
                          uu___))
            | FStar_Reflection_Arith.Neg e1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (152)) (Prims.of_int (8))
                        (Prims.of_int (152)) (Prims.of_int (35)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (153)) (Prims.of_int (8))
                        (Prims.of_int (153)) (Prims.of_int (39)))
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "neg_minus_one"])))))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (canon_point
                                (FStar_Reflection_Arith.Mult
                                   ((FStar_Reflection_Arith.Lit
                                       (Prims.of_int (-1))), e1)))) uu___))
            | FStar_Reflection_Arith.Mult
                (a, FStar_Reflection_Arith.Plus (b, c)) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (157)) (Prims.of_int (8))
                        (Prims.of_int (157)) (Prims.of_int (27)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (158)) (Prims.of_int (8))
                        (Prims.of_int (161)) (Prims.of_int (30)))
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "Canon"; "distr"])))))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (158)) (Prims.of_int (8))
                                   (Prims.of_int (158)) (Prims.of_int (31)))
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (159)) (Prims.of_int (8))
                                   (Prims.of_int (161)) (Prims.of_int (30)))
                                (Obj.magic
                                   (step_lemma
                                      (FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "cong_plus"])))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (159))
                                              (Prims.of_int (16))
                                              (Prims.of_int (159))
                                              (Prims.of_int (38)))
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (160))
                                              (Prims.of_int (8))
                                              (Prims.of_int (161))
                                              (Prims.of_int (30)))
                                           (Obj.magic
                                              (canon_point
                                                 (FStar_Reflection_Arith.Mult
                                                    (a, b))))
                                           (fun uu___2 ->
                                              (fun l ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (160))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (160))
                                                         (Prims.of_int (38)))
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (161))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (161))
                                                         (Prims.of_int (30)))
                                                      (Obj.magic
                                                         (canon_point
                                                            (FStar_Reflection_Arith.Mult
                                                               (a, c))))
                                                      (fun uu___2 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_Arith.Plus
                                                                    (l, r))))
                                                           uu___2))) uu___2)))
                                     uu___1))) uu___))
            | FStar_Reflection_Arith.Mult
                (FStar_Reflection_Arith.Plus (a, b), c) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (164)) (Prims.of_int (8))
                        (Prims.of_int (164)) (Prims.of_int (27)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (165)) (Prims.of_int (8))
                        (Prims.of_int (168)) (Prims.of_int (30)))
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "Canon"; "distl"])))))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (165)) (Prims.of_int (8))
                                   (Prims.of_int (165)) (Prims.of_int (31)))
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (166)) (Prims.of_int (8))
                                   (Prims.of_int (168)) (Prims.of_int (30)))
                                (Obj.magic
                                   (step_lemma
                                      (FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "cong_plus"])))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (166))
                                              (Prims.of_int (16))
                                              (Prims.of_int (166))
                                              (Prims.of_int (38)))
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (167))
                                              (Prims.of_int (8))
                                              (Prims.of_int (168))
                                              (Prims.of_int (30)))
                                           (Obj.magic
                                              (canon_point
                                                 (FStar_Reflection_Arith.Mult
                                                    (a, c))))
                                           (fun uu___2 ->
                                              (fun l ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (167))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (167))
                                                         (Prims.of_int (38)))
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (168))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (168))
                                                         (Prims.of_int (30)))
                                                      (Obj.magic
                                                         (canon_point
                                                            (FStar_Reflection_Arith.Mult
                                                               (b, c))))
                                                      (fun uu___2 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_Arith.Plus
                                                                    (l, r))))
                                                           uu___2))) uu___2)))
                                     uu___1))) uu___))
            | FStar_Reflection_Arith.Mult
                (a, FStar_Reflection_Arith.Mult (b, c)) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (172)) (Prims.of_int (8))
                        (Prims.of_int (172)) (Prims.of_int (32)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (173)) (Prims.of_int (8))
                        (Prims.of_int (176)) (Prims.of_int (30)))
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "ass_mult_l"])))))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (173)) (Prims.of_int (8))
                                   (Prims.of_int (173)) (Prims.of_int (31)))
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (174)) (Prims.of_int (8))
                                   (Prims.of_int (176)) (Prims.of_int (30)))
                                (Obj.magic
                                   (step_lemma
                                      (FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "cong_mult"])))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (174))
                                              (Prims.of_int (16))
                                              (Prims.of_int (174))
                                              (Prims.of_int (38)))
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (175))
                                              (Prims.of_int (8))
                                              (Prims.of_int (176))
                                              (Prims.of_int (30)))
                                           (Obj.magic
                                              (canon_point
                                                 (FStar_Reflection_Arith.Mult
                                                    (a, b))))
                                           (fun uu___2 ->
                                              (fun l ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (175))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (175))
                                                         (Prims.of_int (29)))
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (176))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (176))
                                                         (Prims.of_int (30)))
                                                      (Obj.magic
                                                         (canon_point c))
                                                      (fun uu___2 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_Arith.Mult
                                                                    (l, r))))
                                                           uu___2))) uu___2)))
                                     uu___1))) uu___))
            | FStar_Reflection_Arith.Plus
                (a, FStar_Reflection_Arith.Plus (b, c)) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (179)) (Prims.of_int (8))
                        (Prims.of_int (179)) (Prims.of_int (32)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (180)) (Prims.of_int (8))
                        (Prims.of_int (183)) (Prims.of_int (30)))
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "ass_plus_l"])))))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (180)) (Prims.of_int (8))
                                   (Prims.of_int (180)) (Prims.of_int (31)))
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (181)) (Prims.of_int (8))
                                   (Prims.of_int (183)) (Prims.of_int (30)))
                                (Obj.magic
                                   (step_lemma
                                      (FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "cong_plus"])))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (181))
                                              (Prims.of_int (16))
                                              (Prims.of_int (181))
                                              (Prims.of_int (38)))
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (182))
                                              (Prims.of_int (8))
                                              (Prims.of_int (183))
                                              (Prims.of_int (30)))
                                           (Obj.magic
                                              (canon_point
                                                 (FStar_Reflection_Arith.Plus
                                                    (a, b))))
                                           (fun uu___2 ->
                                              (fun l ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (182))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (182))
                                                         (Prims.of_int (29)))
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (183))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (183))
                                                         (Prims.of_int (30)))
                                                      (Obj.magic
                                                         (canon_point c))
                                                      (fun uu___2 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_Arith.Plus
                                                                    (l, r))))
                                                           uu___2))) uu___2)))
                                     uu___1))) uu___))
            | FStar_Reflection_Arith.Plus
                (FStar_Reflection_Arith.Plus (a, b), c) ->
                if FStar_Order.gt (FStar_Reflection_Arith.compare_expr b c)
                then
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (188)) (Prims.of_int (12))
                          (Prims.of_int (188)) (Prims.of_int (33)))
                       (Prims.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (189)) (Prims.of_int (12))
                          (Prims.of_int (192)) (Prims.of_int (20)))
                       (Obj.magic
                          (step_lemma
                             (FStar_Reflection_Builtins.pack_ln
                                (FStar_Reflection_Data.Tv_FVar
                                   (FStar_Reflection_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "Canon";
                                      "sw_plus"])))))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range "FStar.Tactics.Canon.fst"
                                     (Prims.of_int (189)) (Prims.of_int (12))
                                     (Prims.of_int (189)) (Prims.of_int (36)))
                                  (Prims.mk_range "FStar.Tactics.Canon.fst"
                                     (Prims.of_int (190)) (Prims.of_int (12))
                                     (Prims.of_int (192)) (Prims.of_int (20)))
                                  (Obj.magic
                                     (FStar_Tactics_Derived.apply_lemma
                                        (FStar_Reflection_Builtins.pack_ln
                                           (FStar_Reflection_Data.Tv_FVar
                                              (FStar_Reflection_Builtins.pack_fv
                                                 ["FStar";
                                                 "Tactics";
                                                 "Canon";
                                                 "cong_plus"])))))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.Tactics.Canon.fst"
                                                (Prims.of_int (190))
                                                (Prims.of_int (20))
                                                (Prims.of_int (190))
                                                (Prims.of_int (42)))
                                             (Prims.mk_range
                                                "FStar.Tactics.Canon.fst"
                                                (Prims.of_int (191))
                                                (Prims.of_int (12))
                                                (Prims.of_int (192))
                                                (Prims.of_int (20)))
                                             (Obj.magic
                                                (canon_point
                                                   (FStar_Reflection_Arith.Plus
                                                      (a, c))))
                                             (fun uu___2 ->
                                                (fun l ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Canon.fst"
                                                           (Prims.of_int (191))
                                                           (Prims.of_int (12))
                                                           (Prims.of_int (191))
                                                           (Prims.of_int (19)))
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Canon.fst"
                                                           (Prims.of_int (192))
                                                           (Prims.of_int (12))
                                                           (Prims.of_int (192))
                                                           (Prims.of_int (20)))
                                                        (Obj.magic
                                                           (FStar_Tactics_Derived.trefl
                                                              ()))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                FStar_Reflection_Arith.Plus
                                                                  (l, b)))))
                                                  uu___2))) uu___1))) uu___))
                else Obj.magic (skip ())
            | FStar_Reflection_Arith.Mult
                (FStar_Reflection_Arith.Mult (a, b), c) ->
                if FStar_Order.gt (FStar_Reflection_Arith.compare_expr b c)
                then
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (199)) (Prims.of_int (12))
                          (Prims.of_int (199)) (Prims.of_int (33)))
                       (Prims.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (200)) (Prims.of_int (12))
                          (Prims.of_int (203)) (Prims.of_int (20)))
                       (Obj.magic
                          (step_lemma
                             (FStar_Reflection_Builtins.pack_ln
                                (FStar_Reflection_Data.Tv_FVar
                                   (FStar_Reflection_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "Canon";
                                      "sw_mult"])))))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range "FStar.Tactics.Canon.fst"
                                     (Prims.of_int (200)) (Prims.of_int (12))
                                     (Prims.of_int (200)) (Prims.of_int (36)))
                                  (Prims.mk_range "FStar.Tactics.Canon.fst"
                                     (Prims.of_int (201)) (Prims.of_int (12))
                                     (Prims.of_int (203)) (Prims.of_int (20)))
                                  (Obj.magic
                                     (FStar_Tactics_Derived.apply_lemma
                                        (FStar_Reflection_Builtins.pack_ln
                                           (FStar_Reflection_Data.Tv_FVar
                                              (FStar_Reflection_Builtins.pack_fv
                                                 ["FStar";
                                                 "Tactics";
                                                 "Canon";
                                                 "cong_mult"])))))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.Tactics.Canon.fst"
                                                (Prims.of_int (201))
                                                (Prims.of_int (20))
                                                (Prims.of_int (201))
                                                (Prims.of_int (42)))
                                             (Prims.mk_range
                                                "FStar.Tactics.Canon.fst"
                                                (Prims.of_int (202))
                                                (Prims.of_int (12))
                                                (Prims.of_int (203))
                                                (Prims.of_int (20)))
                                             (Obj.magic
                                                (canon_point
                                                   (FStar_Reflection_Arith.Mult
                                                      (a, c))))
                                             (fun uu___2 ->
                                                (fun l ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Canon.fst"
                                                           (Prims.of_int (202))
                                                           (Prims.of_int (12))
                                                           (Prims.of_int (202))
                                                           (Prims.of_int (20)))
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Canon.fst"
                                                           (Prims.of_int (203))
                                                           (Prims.of_int (12))
                                                           (Prims.of_int (203))
                                                           (Prims.of_int (20)))
                                                        (Obj.magic
                                                           (FStar_Tactics_Derived.trefl
                                                              ()))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                FStar_Reflection_Arith.Mult
                                                                  (l, b)))))
                                                  uu___2))) uu___1))) uu___))
                else Obj.magic (skip ())
            | FStar_Reflection_Arith.Plus
                (a, FStar_Reflection_Arith.Lit uu___) when
                uu___ = Prims.int_zero ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (208)) (Prims.of_int (8))
                        (Prims.of_int (208)) (Prims.of_int (34)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (207)) (Prims.of_int (11))
                        (Prims.of_int (207)) (Prims.of_int (12)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "x_plus_zero"])))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> a)))
            | FStar_Reflection_Arith.Plus
                (FStar_Reflection_Arith.Lit uu___, b) when
                uu___ = Prims.int_zero ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (212)) (Prims.of_int (8))
                        (Prims.of_int (212)) (Prims.of_int (34)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (211)) (Prims.of_int (19))
                        (Prims.of_int (211)) (Prims.of_int (20)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "zero_plus_x"])))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> b)))
            | FStar_Reflection_Arith.Plus (a, b) ->
                if FStar_Order.gt (FStar_Reflection_Arith.compare_expr a b)
                then
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (217)) (Prims.of_int (14))
                          (Prims.of_int (217)) (Prims.of_int (38)))
                       (Prims.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (217)) (Prims.of_int (40))
                          (Prims.of_int (217)) (Prims.of_int (48)))
                       (Obj.magic
                          (FStar_Tactics_Derived.apply_lemma
                             (FStar_Reflection_Builtins.pack_ln
                                (FStar_Reflection_Data.Tv_FVar
                                   (FStar_Reflection_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "Canon";
                                      "comm_plus"])))))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_Reflection_Arith.Plus (b, a))))
                else Obj.magic (skip ())
            | FStar_Reflection_Arith.Mult
                (FStar_Reflection_Arith.Lit uu___, uu___1) when
                uu___ = Prims.int_zero ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (221)) (Prims.of_int (8))
                        (Prims.of_int (221)) (Prims.of_int (34)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (222)) (Prims.of_int (8))
                        (Prims.of_int (222)) (Prims.of_int (13)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "zero_mult_x"])))))
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 ->
                             FStar_Reflection_Arith.Lit Prims.int_zero)))
            | FStar_Reflection_Arith.Mult
                (uu___, FStar_Reflection_Arith.Lit uu___1) when
                uu___1 = Prims.int_zero ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (225)) (Prims.of_int (8))
                        (Prims.of_int (225)) (Prims.of_int (34)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (226)) (Prims.of_int (8))
                        (Prims.of_int (226)) (Prims.of_int (13)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "x_mult_zero"])))))
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 ->
                             FStar_Reflection_Arith.Lit Prims.int_zero)))
            | FStar_Reflection_Arith.Mult
                (FStar_Reflection_Arith.Lit uu___, r) when
                uu___ = Prims.int_one ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (229)) (Prims.of_int (8))
                        (Prims.of_int (229)) (Prims.of_int (33)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (228)) (Prims.of_int (19))
                        (Prims.of_int (228)) (Prims.of_int (20)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "one_mult_x"])))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> r)))
            | FStar_Reflection_Arith.Mult
                (l, FStar_Reflection_Arith.Lit uu___) when
                uu___ = Prims.int_one ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (233)) (Prims.of_int (8))
                        (Prims.of_int (233)) (Prims.of_int (33)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (232)) (Prims.of_int (11))
                        (Prims.of_int (232)) (Prims.of_int (12)))
                     (Obj.magic
                        (FStar_Tactics_Derived.apply_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "x_mult_one"])))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> l)))
            | FStar_Reflection_Arith.Mult (a, b) ->
                if FStar_Order.gt (FStar_Reflection_Arith.compare_expr a b)
                then
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (238)) (Prims.of_int (14))
                          (Prims.of_int (238)) (Prims.of_int (38)))
                       (Prims.mk_range "FStar.Tactics.Canon.fst"
                          (Prims.of_int (238)) (Prims.of_int (40))
                          (Prims.of_int (238)) (Prims.of_int (48)))
                       (Obj.magic
                          (FStar_Tactics_Derived.apply_lemma
                             (FStar_Reflection_Builtins.pack_ln
                                (FStar_Reflection_Data.Tv_FVar
                                   (FStar_Reflection_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "Canon";
                                      "comm_mult"])))))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_Reflection_Arith.Mult (b, a))))
                else Obj.magic (skip ())
            | FStar_Reflection_Arith.Minus (a, b) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (243)) (Prims.of_int (8))
                        (Prims.of_int (243)) (Prims.of_int (35)))
                     (Prims.mk_range "FStar.Tactics.Canon.fst"
                        (Prims.of_int (244)) (Prims.of_int (8))
                        (Prims.of_int (247)) (Prims.of_int (30)))
                     (Obj.magic
                        (step_lemma
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Canon";
                                    "minus_is_plus"])))))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (244)) (Prims.of_int (8))
                                   (Prims.of_int (244)) (Prims.of_int (31)))
                                (Prims.mk_range "FStar.Tactics.Canon.fst"
                                   (Prims.of_int (245)) (Prims.of_int (8))
                                   (Prims.of_int (247)) (Prims.of_int (30)))
                                (Obj.magic
                                   (step_lemma
                                      (FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Tactics";
                                               "Canon";
                                               "cong_plus"])))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (245))
                                              (Prims.of_int (8))
                                              (Prims.of_int (245))
                                              (Prims.of_int (16)))
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (246))
                                              (Prims.of_int (8))
                                              (Prims.of_int (247))
                                              (Prims.of_int (30)))
                                           (Obj.magic
                                              (FStar_Tactics_Derived.trefl ()))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (246))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (246))
                                                         (Prims.of_int (35)))
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Canon.fst"
                                                         (Prims.of_int (247))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (247))
                                                         (Prims.of_int (30)))
                                                      (Obj.magic
                                                         (canon_point
                                                            (FStar_Reflection_Arith.Neg
                                                               b)))
                                                      (fun uu___3 ->
                                                         (fun r ->
                                                            Obj.magic
                                                              (canon_point
                                                                 (FStar_Reflection_Arith.Plus
                                                                    (a, r))))
                                                           uu___3))) uu___2)))
                                     uu___1))) uu___))
            | uu___ -> Obj.magic (skip ())) uu___)
let (canon_point_entry : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Canon.fst" (Prims.of_int (264))
         (Prims.of_int (4)) (Prims.of_int (264)) (Prims.of_int (11)))
      (Prims.mk_range "FStar.Tactics.Canon.fst" (Prims.of_int (265))
         (Prims.of_int (4)) (Prims.of_int (273)) (Prims.of_int (48)))
      (Obj.magic (FStar_Tactics_Builtins.norm []))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Canon.fst"
                    (Prims.of_int (265)) (Prims.of_int (12))
                    (Prims.of_int (265)) (Prims.of_int (23)))
                 (Prims.mk_range "FStar.Tactics.Canon.fst"
                    (Prims.of_int (266)) (Prims.of_int (4))
                    (Prims.of_int (273)) (Prims.of_int (48)))
                 (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                 (fun uu___2 ->
                    (fun g ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range "FStar.Tactics.Canon.fst"
                               (Prims.of_int (266)) (Prims.of_int (10))
                               (Prims.of_int (266)) (Prims.of_int (27)))
                            (Prims.mk_range "FStar.Tactics.Canon.fst"
                               (Prims.of_int (266)) (Prims.of_int (4))
                               (Prims.of_int (273)) (Prims.of_int (48)))
                            (Obj.magic
                               (FStar_Reflection_Formula.term_as_formula g))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  match uu___2 with
                                  | FStar_Reflection_Formula.Comp
                                      (FStar_Reflection_Formula.Eq uu___3, l,
                                       r)
                                      ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (268))
                                              (Prims.of_int (20))
                                              (Prims.of_int (268))
                                              (Prims.of_int (44)))
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (268))
                                              (Prims.of_int (14))
                                              (Prims.of_int (270))
                                              (Prims.of_int (27)))
                                           (Obj.magic
                                              (FStar_Reflection_Arith.run_tm
                                                 (FStar_Reflection_Arith.is_arith_expr
                                                    l)))
                                           (fun uu___4 ->
                                              (fun uu___4 ->
                                                 match uu___4 with
                                                 | FStar_Pervasives.Inr e ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Canon.fst"
                                                             (Prims.of_int (269))
                                                             (Prims.of_int (29))
                                                             (Prims.of_int (269))
                                                             (Prims.of_int (42)))
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Canon.fst"
                                                             (Prims.of_int (269))
                                                             (Prims.of_int (46))
                                                             (Prims.of_int (269))
                                                             (Prims.of_int (48)))
                                                          (Obj.magic
                                                             (canon_point e))
                                                          (fun _e ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___5 ->
                                                                  ())))
                                                 | FStar_Pervasives.Inl
                                                     uu___5 ->
                                                     Obj.magic
                                                       (FStar_Tactics_Derived.trefl
                                                          ())) uu___4))
                                  | uu___3 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (273))
                                              (Prims.of_int (13))
                                              (Prims.of_int (273))
                                              (Prims.of_int (48)))
                                           (Prims.mk_range
                                              "FStar.Tactics.Canon.fst"
                                              (Prims.of_int (273))
                                              (Prims.of_int (8))
                                              (Prims.of_int (273))
                                              (Prims.of_int (48)))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Canon.fst"
                                                    (Prims.of_int (273))
                                                    (Prims.of_int (31))
                                                    (Prims.of_int (273))
                                                    (Prims.of_int (47)))
                                                 (Prims.mk_range "prims.fst"
                                                    (Prims.of_int (606))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (606))
                                                    (Prims.of_int (31)))
                                                 (Obj.magic
                                                    (FStar_Tactics_Builtins.term_to_string
                                                       g))
                                                 (fun uu___4 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___5 ->
                                                         Prims.strcat
                                                           "impossible: "
                                                           uu___4))))
                                           (fun uu___4 ->
                                              (fun uu___4 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Derived.fail
                                                      uu___4)) uu___4)))
                                 uu___2))) uu___2))) uu___1)
let (canon : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStar_Tactics_Derived.pointwise canon_point_entry