open Prims
let (tiff : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Simplifier"; "lem_iff_refl"])))
let (step : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Simplifier"; "lem_iff_trans"])))
let (is_true :
  FStar_Tactics_NamedView.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Reflection_V2_Formula.term_as_formula' t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (159)) (Prims.of_int (16)) (Prims.of_int (159))
               (Prims.of_int (34)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (159)) (Prims.of_int (10)) (Prims.of_int (172))
               (Prims.of_int (14))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Reflection_V2_Formula.True_ ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> true)))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 = FStar_Tactics_NamedView.inspect t in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Simplifier.fst"
                                 (Prims.of_int (161)) (Prims.of_int (23))
                                 (Prims.of_int (161)) (Prims.of_int (32)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Simplifier.fst"
                                 (Prims.of_int (161)) (Prims.of_int (17))
                                 (Prims.of_int (171)) (Prims.of_int (23)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              match uu___4 with
                              | FStar_Tactics_NamedView.Tv_App (l, r) ->
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___5 =
                                          FStar_Tactics_NamedView.inspect l in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Simplifier.fst"
                                                   (Prims.of_int (163))
                                                   (Prims.of_int (24))
                                                   (Prims.of_int (163))
                                                   (Prims.of_int (33)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Simplifier.fst"
                                                   (Prims.of_int (163))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (169))
                                                   (Prims.of_int (24)))))
                                          (Obj.magic uu___5)
                                          (fun uu___6 ->
                                             (fun uu___6 ->
                                                match uu___6 with
                                                | FStar_Tactics_NamedView.Tv_Abs
                                                    (b, t1) ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (let uu___7 =
                                                            FStar_Reflection_V2_Formula.term_as_formula'
                                                              t1 in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (46)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (28)))))
                                                            (Obj.magic uu___7)
                                                            (fun uu___8 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___9
                                                                    ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Formula.True_
                                                                    -> true
                                                                    | 
                                                                    uu___10
                                                                    -> false))))
                                                | uu___7 ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___8 ->
                                                               false))))
                                               uu___6)))
                              | uu___5 ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___6 -> false)))) uu___4))))
           uu___1)
let (is_false :
  FStar_Tactics_NamedView.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Reflection_V2_Formula.term_as_formula' t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (177)) (Prims.of_int (16)) (Prims.of_int (177))
               (Prims.of_int (34)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (177)) (Prims.of_int (10)) (Prims.of_int (190))
               (Prims.of_int (14))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Reflection_V2_Formula.False_ ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> true)))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 = FStar_Tactics_NamedView.inspect t in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Simplifier.fst"
                                 (Prims.of_int (179)) (Prims.of_int (23))
                                 (Prims.of_int (179)) (Prims.of_int (32)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Simplifier.fst"
                                 (Prims.of_int (179)) (Prims.of_int (17))
                                 (Prims.of_int (189)) (Prims.of_int (23)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              match uu___4 with
                              | FStar_Tactics_NamedView.Tv_App (l, r) ->
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___5 =
                                          FStar_Tactics_NamedView.inspect l in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Simplifier.fst"
                                                   (Prims.of_int (181))
                                                   (Prims.of_int (24))
                                                   (Prims.of_int (181))
                                                   (Prims.of_int (33)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Simplifier.fst"
                                                   (Prims.of_int (181))
                                                   (Prims.of_int (18))
                                                   (Prims.of_int (187))
                                                   (Prims.of_int (24)))))
                                          (Obj.magic uu___5)
                                          (fun uu___6 ->
                                             (fun uu___6 ->
                                                match uu___6 with
                                                | FStar_Tactics_NamedView.Tv_Abs
                                                    (b, t1) ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (let uu___7 =
                                                            FStar_Reflection_V2_Formula.term_as_formula'
                                                              t1 in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (46)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (28)))))
                                                            (Obj.magic uu___7)
                                                            (fun uu___8 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___9
                                                                    ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Formula.False_
                                                                    -> true
                                                                    | 
                                                                    uu___10
                                                                    -> false))))
                                                | uu___7 ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___8 ->
                                                               false))))
                                               uu___6)))
                              | uu___5 ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___6 -> false)))) uu___4))))
           uu___1)
let (inhabit : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStar_Tactics_V2_Derived.cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (195)) (Prims.of_int (12)) (Prims.of_int (195))
               (Prims.of_int (23)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (196)) (Prims.of_int (4)) (Prims.of_int (203))
               (Prims.of_int (18))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun t ->
            let uu___2 = FStar_Tactics_NamedView.inspect t in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (196)) (Prims.of_int (10))
                          (Prims.of_int (196)) (Prims.of_int (19)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (196)) (Prims.of_int (4))
                          (Prims.of_int (203)) (Prims.of_int (18)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_Tactics_NamedView.Tv_FVar fv ->
                           Obj.magic
                             (Obj.repr
                                (let uu___4 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 ->
                                           FStarC_Reflection_V2_Builtins.inspect_fv
                                             fv)) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Simplifier.fst"
                                            (Prims.of_int (198))
                                            (Prims.of_int (17))
                                            (Prims.of_int (198))
                                            (Prims.of_int (30)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Simplifier.fst"
                                            (Prims.of_int (199))
                                            (Prims.of_int (13))
                                            (Prims.of_int (202))
                                            (Prims.of_int (20)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      (fun qn ->
                                         if
                                           qn =
                                             FStar_Reflection_Const.int_lid
                                         then
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_V2_Derived.exact
                                                   (FStarC_Reflection_V2_Builtins.pack_ln
                                                      (FStarC_Reflection_V2_Data.Tv_Const
                                                         (FStarC_Reflection_V2_Data.C_Int
                                                            (Prims.of_int (42)))))))
                                         else
                                           Obj.magic
                                             (Obj.repr
                                                (if
                                                   qn =
                                                     FStar_Reflection_Const.bool_lid
                                                 then
                                                   Obj.repr
                                                     (FStar_Tactics_V2_Derived.exact
                                                        (FStarC_Reflection_V2_Builtins.pack_ln
                                                           (FStarC_Reflection_V2_Data.Tv_Const
                                                              FStarC_Reflection_V2_Data.C_True)))
                                                 else
                                                   Obj.repr
                                                     (if
                                                        qn =
                                                          FStar_Reflection_Const.unit_lid
                                                      then
                                                        Obj.repr
                                                          (FStar_Tactics_V2_Derived.exact
                                                             (FStarC_Reflection_V2_Builtins.pack_ln
                                                                (FStarC_Reflection_V2_Data.Tv_Const
                                                                   FStarC_Reflection_V2_Data.C_Unit)))
                                                      else
                                                        Obj.repr
                                                          (FStar_Tactics_V2_Derived.fail
                                                             ""))))) uu___5)))
                       | uu___4 ->
                           Obj.magic
                             (Obj.repr (FStar_Tactics_V2_Derived.fail "")))
                      uu___3))) uu___2)
let rec (simplify_point : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = recurse () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (209)) (Prims.of_int (4)) (Prims.of_int (209))
               (Prims.of_int (14)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (210)) (Prims.of_int (4)) (Prims.of_int (264))
               (Prims.of_int (81))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 = FStarC_Tactics_V2_Builtins.norm [] in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (210)) (Prims.of_int (4))
                          (Prims.of_int (210)) (Prims.of_int (11)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (210)) (Prims.of_int (12))
                          (Prims.of_int (264)) (Prims.of_int (81)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun uu___4 ->
                       let uu___5 = FStar_Tactics_V2_Derived.cur_goal () in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Simplifier.fst"
                                     (Prims.of_int (211)) (Prims.of_int (12))
                                     (Prims.of_int (211)) (Prims.of_int (23)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Simplifier.fst"
                                     (Prims.of_int (211)) (Prims.of_int (26))
                                     (Prims.of_int (264)) (Prims.of_int (81)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               (fun g ->
                                  let uu___6 =
                                    FStar_Reflection_V2_Formula.term_as_formula
                                      g in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Simplifier.fst"
                                                (Prims.of_int (212))
                                                (Prims.of_int (12))
                                                (Prims.of_int (212))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Simplifier.fst"
                                                (Prims.of_int (213))
                                                (Prims.of_int (4))
                                                (Prims.of_int (264))
                                                (Prims.of_int (81)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          (fun f ->
                                             match f with
                                             | FStar_Reflection_V2_Formula.Iff
                                                 (l, r) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (let uu___7 =
                                                         FStar_Reflection_V2_Formula.term_as_formula'
                                                           l in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Simplifier.fst"
                                                                  (Prims.of_int (215))
                                                                  (Prims.of_int (20))
                                                                  (Prims.of_int (215))
                                                                  (Prims.of_int (38)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Simplifier.fst"
                                                                  (Prims.of_int (215))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (262))
                                                                  (Prims.of_int (22)))))
                                                         (Obj.magic uu___7)
                                                         (fun uu___8 ->
                                                            (fun uu___8 ->
                                                               match uu___8
                                                               with
                                                               | FStar_Reflection_V2_Formula.And
                                                                   (p, q) ->
                                                                   let uu___9
                                                                    =
                                                                    is_true p in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_and_p"]))))
                                                                    else
                                                                    (let uu___12
                                                                    =
                                                                    is_true q in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_and_true"]))))
                                                                    else
                                                                    (let uu___15
                                                                    =
                                                                    is_false
                                                                    p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    if
                                                                    uu___16
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_and_p"]))))
                                                                    else
                                                                    (let uu___18
                                                                    =
                                                                    is_false
                                                                    q in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    if
                                                                    uu___19
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_and_false"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___19))))
                                                                    uu___16))))
                                                                    uu___13))))
                                                                    uu___10))
                                                               | FStar_Reflection_V2_Formula.Or
                                                                   (p, q) ->
                                                                   let uu___9
                                                                    =
                                                                    is_true p in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_or_p"]))))
                                                                    else
                                                                    (let uu___12
                                                                    =
                                                                    is_true q in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_or_true"]))))
                                                                    else
                                                                    (let uu___15
                                                                    =
                                                                    is_false
                                                                    p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    if
                                                                    uu___16
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_or_p"]))))
                                                                    else
                                                                    (let uu___18
                                                                    =
                                                                    is_false
                                                                    q in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    if
                                                                    uu___19
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_or_false"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___19))))
                                                                    uu___16))))
                                                                    uu___13))))
                                                                    uu___10))
                                                               | FStar_Reflection_V2_Formula.Implies
                                                                   (p, q) ->
                                                                   let uu___9
                                                                    =
                                                                    is_true p in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_imp_p"]))))
                                                                    else
                                                                    (let uu___12
                                                                    =
                                                                    is_true q in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_imp_true"]))))
                                                                    else
                                                                    (let uu___15
                                                                    =
                                                                    is_false
                                                                    p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    if
                                                                    uu___16
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_imp_p"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___16))))
                                                                    uu___13))))
                                                                    uu___10))
                                                               | FStar_Reflection_V2_Formula.Forall
                                                                   (_b,
                                                                    _sort, p)
                                                                   ->
                                                                   let uu___9
                                                                    =
                                                                    is_true p in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_fa_true"]))))
                                                                    else
                                                                    (let uu___12
                                                                    =
                                                                    is_false
                                                                    p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.or_else
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_fa_false"]))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (94)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (inhabit
                                                                    ()))
                                                                    uu___16))
                                                                    tiff)
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___13))))
                                                                    uu___10))
                                                               | FStar_Reflection_V2_Formula.Exists
                                                                   (_b,
                                                                    _sort, p)
                                                                   ->
                                                                   let uu___9
                                                                    =
                                                                    is_false
                                                                    p in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_ex_false"]))))
                                                                    else
                                                                    (let uu___12
                                                                    =
                                                                    is_true p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.or_else
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_ex_true"]))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (93)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (inhabit
                                                                    ()))
                                                                    uu___16))
                                                                    tiff)
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___13))))
                                                                    uu___10))
                                                               | FStar_Reflection_V2_Formula.Not
                                                                   p ->
                                                                   let uu___9
                                                                    =
                                                                    is_true p in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_neg_true"]))))
                                                                    else
                                                                    (let uu___12
                                                                    =
                                                                    is_false
                                                                    p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_neg_false"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___13))))
                                                                    uu___10))
                                                               | FStar_Reflection_V2_Formula.Iff
                                                                   (p, q) ->
                                                                   let uu___9
                                                                    = 
                                                                    step () in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (29)))))
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
                                                                    is_true p in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_iff_p"]))))
                                                                    else
                                                                    (let uu___15
                                                                    =
                                                                    is_true q in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    if
                                                                    uu___16
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_iff_true"]))))
                                                                    else
                                                                    (let uu___18
                                                                    =
                                                                    is_false
                                                                    p in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    if
                                                                    uu___19
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_iff_p"]))))
                                                                    else
                                                                    (let uu___21
                                                                    =
                                                                    is_false
                                                                    q in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    if
                                                                    uu___22
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_iff_false"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___22))))
                                                                    uu___19))))
                                                                    uu___16))))
                                                                    uu___13) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (simplify_point
                                                                    ()))
                                                                    uu___12)))
                                                                    uu___10))
                                                               | uu___9 ->
                                                                   Obj.magic
                                                                    (tiff ()))
                                                              uu___8)))
                                             | uu___7 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_V2_Derived.fail
                                                         "simplify_point: failed precondition: goal should be `g <==> ?u`")))
                                            uu___7))) uu___6))) uu___4)))
           uu___2)
and (recurse : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = step () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (267)) (Prims.of_int (4)) (Prims.of_int (267))
               (Prims.of_int (11)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (268)) (Prims.of_int (4)) (Prims.of_int (302))
               (Prims.of_int (74))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 = FStarC_Tactics_V2_Builtins.norm [] in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (268)) (Prims.of_int (4))
                          (Prims.of_int (268)) (Prims.of_int (11)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
                          (Prims.of_int (268)) (Prims.of_int (12))
                          (Prims.of_int (302)) (Prims.of_int (74)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun uu___4 ->
                       let uu___5 = FStar_Tactics_V2_Derived.cur_goal () in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Simplifier.fst"
                                     (Prims.of_int (269)) (Prims.of_int (12))
                                     (Prims.of_int (269)) (Prims.of_int (23)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Simplifier.fst"
                                     (Prims.of_int (269)) (Prims.of_int (26))
                                     (Prims.of_int (302)) (Prims.of_int (74)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               (fun g ->
                                  let uu___6 =
                                    FStar_Reflection_V2_Formula.term_as_formula
                                      g in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Simplifier.fst"
                                                (Prims.of_int (270))
                                                (Prims.of_int (12))
                                                (Prims.of_int (270))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Simplifier.fst"
                                                (Prims.of_int (271))
                                                (Prims.of_int (4))
                                                (Prims.of_int (302))
                                                (Prims.of_int (74)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          (fun f ->
                                             match f with
                                             | FStar_Reflection_V2_Formula.Iff
                                                 (l, r) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (let uu___7 =
                                                         FStar_Reflection_V2_Formula.term_as_formula'
                                                           l in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Simplifier.fst"
                                                                  (Prims.of_int (273))
                                                                  (Prims.of_int (20))
                                                                  (Prims.of_int (273))
                                                                  (Prims.of_int (38)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Simplifier.fst"
                                                                  (Prims.of_int (273))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (300))
                                                                  (Prims.of_int (22)))))
                                                         (Obj.magic uu___7)
                                                         (fun uu___8 ->
                                                            (fun uu___8 ->
                                                               match uu___8
                                                               with
                                                               | FStar_Reflection_V2_Formula.And
                                                                   (uu___9,
                                                                    uu___10)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_V2_Derived.seq
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "and_cong"]))))
                                                                    simplify_point)
                                                               | FStar_Reflection_V2_Formula.Or
                                                                   (uu___9,
                                                                    uu___10)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_V2_Derived.seq
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "or_cong"]))))
                                                                    simplify_point)
                                                               | FStar_Reflection_V2_Formula.Implies
                                                                   (uu___9,
                                                                    uu___10)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_V2_Derived.seq
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "imp_cong"]))))
                                                                    simplify_point)
                                                               | FStar_Reflection_V2_Formula.Forall
                                                                   (uu___9,
                                                                    uu___10,
                                                                    uu___11)
                                                                   ->
                                                                   let uu___12
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "fa_cong"]))) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (29)))))
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
                                                                    FStarC_Tactics_V2_Builtins.intro
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (simplify_point
                                                                    ()))
                                                                    uu___15)))
                                                                    uu___13))
                                                               | FStar_Reflection_V2_Formula.Exists
                                                                   (uu___9,
                                                                    uu___10,
                                                                    uu___11)
                                                                   ->
                                                                   let uu___12
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "ex_cong"]))) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (29)))))
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
                                                                    FStarC_Tactics_V2_Builtins.intro
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (simplify_point
                                                                    ()))
                                                                    uu___15)))
                                                                    uu___13))
                                                               | FStar_Reflection_V2_Formula.Not
                                                                   uu___9 ->
                                                                   let uu___10
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "neg_cong"]))) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (simplify_point
                                                                    ()))
                                                                    uu___11))
                                                               | FStar_Reflection_V2_Formula.Iff
                                                                   (uu___9,
                                                                    uu___10)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_V2_Derived.seq
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "iff_cong"]))))
                                                                    simplify_point)
                                                               | uu___9 ->
                                                                   Obj.magic
                                                                    (tiff ()))
                                                              uu___8)))
                                             | uu___7 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_V2_Derived.fail
                                                         "recurse: failed precondition: goal should be `g <==> ?u`")))
                                            uu___7))) uu___6))) uu___4)))
           uu___2)
let (simplify : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_V2_Derived.apply_lemma
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar"; "Tactics"; "Simplifier"; "equiv"]))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (308)) (Prims.of_int (4)) (Prims.of_int (308))
               (Prims.of_int (24)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Simplifier.fst"
               (Prims.of_int (309)) (Prims.of_int (4)) (Prims.of_int (309))
               (Prims.of_int (21))))) (Obj.magic uu___1)
      (fun uu___2 -> (fun uu___2 -> Obj.magic (simplify_point ())) uu___2)