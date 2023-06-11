open Prims
let (tiff : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Simplifier"; "lem_iff_refl"])))
let (step : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Simplifier"; "lem_iff_trans"])))
let (is_true :
  FStar_Tactics_NamedView.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
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
               (Prims.of_int (14)))))
      (Obj.magic (FStar_Reflection_V2_Formula.term_as_formula' t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_V2_Formula.True_ ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> true)))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
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
                        (Obj.magic (FStar_Tactics_NamedView.inspect t))
                        (fun uu___2 ->
                           (fun uu___2 ->
                              match uu___2 with
                              | FStar_Tactics_NamedView.Tv_App (l, r) ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
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
                                          (Obj.magic
                                             (FStar_Tactics_NamedView.inspect
                                                l))
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                match uu___3 with
                                                | FStar_Tactics_NamedView.Tv_Abs
                                                    (b, t1) ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.tac_bind
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
                                                            (Obj.magic
                                                               (FStar_Reflection_V2_Formula.term_as_formula'
                                                                  t1))
                                                            (fun uu___4 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___5
                                                                    ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Formula.True_
                                                                    -> true
                                                                    | 
                                                                    uu___6 ->
                                                                    false))))
                                                | uu___4 ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___5 ->
                                                               false))))
                                               uu___3)))
                              | uu___3 ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 -> false)))) uu___2))))
           uu___)
let (is_false :
  FStar_Tactics_NamedView.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
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
               (Prims.of_int (14)))))
      (Obj.magic (FStar_Reflection_V2_Formula.term_as_formula' t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_V2_Formula.False_ ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> true)))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
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
                        (Obj.magic (FStar_Tactics_NamedView.inspect t))
                        (fun uu___2 ->
                           (fun uu___2 ->
                              match uu___2 with
                              | FStar_Tactics_NamedView.Tv_App (l, r) ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
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
                                          (Obj.magic
                                             (FStar_Tactics_NamedView.inspect
                                                l))
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                match uu___3 with
                                                | FStar_Tactics_NamedView.Tv_Abs
                                                    (b, t1) ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.tac_bind
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
                                                            (Obj.magic
                                                               (FStar_Reflection_V2_Formula.term_as_formula'
                                                                  t1))
                                                            (fun uu___4 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___5
                                                                    ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Formula.False_
                                                                    -> true
                                                                    | 
                                                                    uu___6 ->
                                                                    false))))
                                                | uu___4 ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___5 ->
                                                               false))))
                                               uu___3)))
                              | uu___3 ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 -> false)))) uu___2))))
           uu___)
let (inhabit : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
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
               (Prims.of_int (18)))))
      (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
      (fun uu___1 ->
         (fun t ->
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
                 (Obj.magic (FStar_Tactics_NamedView.inspect t))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       match uu___1 with
                       | FStar_Tactics_NamedView.Tv_FVar fv ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
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
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         FStar_Reflection_V2_Builtins.inspect_fv
                                           fv))
                                   (fun uu___2 ->
                                      (fun qn ->
                                         if
                                           qn =
                                             FStar_Reflection_Const.int_lid
                                         then
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_V2_Derived.exact
                                                   (FStar_Reflection_V2_Builtins.pack_ln
                                                      (FStar_Reflection_V2_Data.Tv_Const
                                                         (FStar_Reflection_V2_Data.C_Int
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
                                                        (FStar_Reflection_V2_Builtins.pack_ln
                                                           (FStar_Reflection_V2_Data.Tv_Const
                                                              FStar_Reflection_V2_Data.C_True)))
                                                 else
                                                   Obj.repr
                                                     (if
                                                        qn =
                                                          FStar_Reflection_Const.unit_lid
                                                      then
                                                        Obj.repr
                                                          (FStar_Tactics_V2_Derived.exact
                                                             (FStar_Reflection_V2_Builtins.pack_ln
                                                                (FStar_Reflection_V2_Data.Tv_Const
                                                                   FStar_Reflection_V2_Data.C_Unit)))
                                                      else
                                                        Obj.repr
                                                          (FStar_Tactics_V2_Derived.fail
                                                             ""))))) uu___2)))
                       | uu___2 ->
                           Obj.magic
                             (Obj.repr (FStar_Tactics_V2_Derived.fail "")))
                      uu___1))) uu___1)
let rec (simplify_point : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
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
               (Prims.of_int (81))))) (Obj.magic (recurse ()))
      (fun uu___1 ->
         (fun uu___1 ->
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
                 (Obj.magic (FStar_Tactics_V2_Builtins.norm []))
                 (fun uu___2 ->
                    (fun uu___2 ->
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
                            (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
                            (fun uu___3 ->
                               (fun g ->
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
                                       (Obj.magic
                                          (FStar_Reflection_V2_Formula.term_as_formula
                                             g))
                                       (fun uu___3 ->
                                          (fun f ->
                                             match f with
                                             | FStar_Reflection_V2_Formula.Iff
                                                 (l, r) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.tac_bind
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
                                                         (Obj.magic
                                                            (FStar_Reflection_V2_Formula.term_as_formula'
                                                               l))
                                                         (fun uu___3 ->
                                                            (fun uu___3 ->
                                                               match uu___3
                                                               with
                                                               | FStar_Reflection_V2_Formula.And
                                                                   (p, q) ->
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
                                                                    (is_true
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    if uu___4
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_and_p"]))))
                                                                    else
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
                                                                    (is_true
                                                                    q))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_and_true"]))))
                                                                    else
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
                                                                    (is_false
                                                                    p))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    if uu___8
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_and_p"]))))
                                                                    else
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
                                                                    (is_false
                                                                    q))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_and_false"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___4))
                                                               | FStar_Reflection_V2_Formula.Or
                                                                   (p, q) ->
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
                                                                    (is_true
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    if uu___4
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_or_p"]))))
                                                                    else
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
                                                                    (is_true
                                                                    q))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_or_true"]))))
                                                                    else
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
                                                                    (is_false
                                                                    p))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    if uu___8
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_or_p"]))))
                                                                    else
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
                                                                    (is_false
                                                                    q))
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
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_or_false"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___4))
                                                               | FStar_Reflection_V2_Formula.Implies
                                                                   (p, q) ->
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
                                                                    (is_true
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    if uu___4
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_imp_p"]))))
                                                                    else
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
                                                                    (is_true
                                                                    q))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_imp_true"]))))
                                                                    else
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
                                                                    (is_false
                                                                    p))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    if uu___8
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_imp_p"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___4))
                                                               | FStar_Reflection_V2_Formula.Forall
                                                                   (_b,
                                                                    _sort, p)
                                                                   ->
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
                                                                    (is_true
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    if uu___4
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_fa_true"]))))
                                                                    else
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
                                                                    (is_false
                                                                    p))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.or_else
                                                                    (fun
                                                                    uu___7 ->
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
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_fa_false"])))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (inhabit
                                                                    ()))
                                                                    uu___8))
                                                                    tiff)
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___6)))
                                                                    uu___4))
                                                               | FStar_Reflection_V2_Formula.Exists
                                                                   (_b,
                                                                    _sort, p)
                                                                   ->
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
                                                                    (is_false
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    if uu___4
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_ex_false"]))))
                                                                    else
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
                                                                    (is_true
                                                                    p))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.or_else
                                                                    (fun
                                                                    uu___7 ->
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
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_ex_true"])))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (inhabit
                                                                    ()))
                                                                    uu___8))
                                                                    tiff)
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___6)))
                                                                    uu___4))
                                                               | FStar_Reflection_V2_Formula.Not
                                                                   p ->
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
                                                                    (is_true
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    if uu___4
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_neg_true"]))))
                                                                    else
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
                                                                    (is_false
                                                                    p))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_neg_false"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___6)))
                                                                    uu___4))
                                                               | FStar_Reflection_V2_Formula.Iff
                                                                   (p, q) ->
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
                                                                    (step ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
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
                                                                    (FStar_Tactics_Effect.tac_bind
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
                                                                    (is_true
                                                                    p))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    if uu___5
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_iff_p"]))))
                                                                    else
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
                                                                    (is_true
                                                                    q))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    if uu___7
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_iff_true"]))))
                                                                    else
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
                                                                    (is_false
                                                                    p))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    if uu___9
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_iff_p"]))))
                                                                    else
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
                                                                    (is_false
                                                                    q))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    if
                                                                    uu___11
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_iff_false"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    uu___7)))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (simplify_point
                                                                    ()))
                                                                    uu___5)))
                                                                    uu___4))
                                                               | uu___4 ->
                                                                   Obj.magic
                                                                    (tiff ()))
                                                              uu___3)))
                                             | uu___3 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_V2_Derived.fail
                                                         "simplify_point: failed precondition: goal should be `g <==> ?u`")))
                                            uu___3))) uu___3))) uu___2)))
           uu___1)
and (recurse : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
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
               (Prims.of_int (74))))) (Obj.magic (step ()))
      (fun uu___1 ->
         (fun uu___1 ->
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
                 (Obj.magic (FStar_Tactics_V2_Builtins.norm []))
                 (fun uu___2 ->
                    (fun uu___2 ->
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
                            (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
                            (fun uu___3 ->
                               (fun g ->
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
                                       (Obj.magic
                                          (FStar_Reflection_V2_Formula.term_as_formula
                                             g))
                                       (fun uu___3 ->
                                          (fun f ->
                                             match f with
                                             | FStar_Reflection_V2_Formula.Iff
                                                 (l, r) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.tac_bind
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
                                                         (Obj.magic
                                                            (FStar_Reflection_V2_Formula.term_as_formula'
                                                               l))
                                                         (fun uu___3 ->
                                                            (fun uu___3 ->
                                                               match uu___3
                                                               with
                                                               | FStar_Reflection_V2_Formula.And
                                                                   (uu___4,
                                                                    uu___5)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_V2_Derived.seq
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "and_cong"]))))
                                                                    simplify_point)
                                                               | FStar_Reflection_V2_Formula.Or
                                                                   (uu___4,
                                                                    uu___5)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_V2_Derived.seq
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "or_cong"]))))
                                                                    simplify_point)
                                                               | FStar_Reflection_V2_Formula.Implies
                                                                   (uu___4,
                                                                    uu___5)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_V2_Derived.seq
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "imp_cong"]))))
                                                                    simplify_point)
                                                               | FStar_Reflection_V2_Formula.Forall
                                                                   (uu___4,
                                                                    uu___5,
                                                                    uu___6)
                                                                   ->
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
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "fa_cong"])))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
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
                                                                    (FStar_Tactics_V2_Builtins.intro
                                                                    ()))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (simplify_point
                                                                    ()))
                                                                    uu___8)))
                                                                    uu___7))
                                                               | FStar_Reflection_V2_Formula.Exists
                                                                   (uu___4,
                                                                    uu___5,
                                                                    uu___6)
                                                                   ->
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
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "ex_cong"])))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
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
                                                                    (FStar_Tactics_V2_Builtins.intro
                                                                    ()))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (simplify_point
                                                                    ()))
                                                                    uu___8)))
                                                                    uu___7))
                                                               | FStar_Reflection_V2_Formula.Not
                                                                   uu___4 ->
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
                                                                    (FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "neg_cong"])))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (simplify_point
                                                                    ()))
                                                                    uu___5))
                                                               | FStar_Reflection_V2_Formula.Iff
                                                                   (uu___4,
                                                                    uu___5)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_V2_Derived.seq
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "iff_cong"]))))
                                                                    simplify_point)
                                                               | uu___4 ->
                                                                   Obj.magic
                                                                    (tiff ()))
                                                              uu___3)))
                                             | uu___3 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_V2_Derived.fail
                                                         "recurse: failed precondition: goal should be `g <==> ?u`")))
                                            uu___3))) uu___3))) uu___2)))
           uu___1)
let (simplify : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
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
               (Prims.of_int (21)))))
      (Obj.magic
         (FStar_Tactics_V2_Derived.apply_lemma
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Simplifier"; "equiv"])))))
      (fun uu___1 -> (fun uu___1 -> Obj.magic (simplify_point ())) uu___1)