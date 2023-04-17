open Prims
let (tiff : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Derived.apply_lemma
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Tactics"; "Simplifier"; "lem_iff_refl"])))
let (step : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Derived.apply_lemma
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Tactics"; "Simplifier"; "lem_iff_trans"])))
let (is_true :
  FStar_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (161))
         (Prims.of_int (16)) (Prims.of_int (161)) (Prims.of_int (34)))
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (161))
         (Prims.of_int (10)) (Prims.of_int (174)) (Prims.of_int (14)))
      (Obj.magic (FStar_Reflection_Formula.term_as_formula' t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Formula.True_ ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> true)))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                           (Prims.of_int (163)) (Prims.of_int (23))
                           (Prims.of_int (163)) (Prims.of_int (32)))
                        (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                           (Prims.of_int (163)) (Prims.of_int (17))
                           (Prims.of_int (173)) (Prims.of_int (23)))
                        (Obj.magic (FStar_Tactics_Builtins.inspect t))
                        (fun uu___2 ->
                           (fun uu___2 ->
                              match uu___2 with
                              | FStar_Reflection_Data.Tv_App (l, r) ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Tactics.Simplifier.fst"
                                             (Prims.of_int (165))
                                             (Prims.of_int (24))
                                             (Prims.of_int (165))
                                             (Prims.of_int (33)))
                                          (Prims.mk_range
                                             "FStar.Tactics.Simplifier.fst"
                                             (Prims.of_int (165))
                                             (Prims.of_int (18))
                                             (Prims.of_int (171))
                                             (Prims.of_int (24)))
                                          (Obj.magic
                                             (FStar_Tactics_Builtins.inspect
                                                l))
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                match uu___3 with
                                                | FStar_Reflection_Data.Tv_Abs
                                                    (b, t1) ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Simplifier.fst"
                                                               (Prims.of_int (167))
                                                               (Prims.of_int (28))
                                                               (Prims.of_int (167))
                                                               (Prims.of_int (46)))
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Simplifier.fst"
                                                               (Prims.of_int (167))
                                                               (Prims.of_int (22))
                                                               (Prims.of_int (169))
                                                               (Prims.of_int (28)))
                                                            (Obj.magic
                                                               (FStar_Reflection_Formula.term_as_formula'
                                                                  t1))
                                                            (fun uu___4 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___5
                                                                    ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Formula.True_
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
  FStar_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (179))
         (Prims.of_int (16)) (Prims.of_int (179)) (Prims.of_int (34)))
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (179))
         (Prims.of_int (10)) (Prims.of_int (192)) (Prims.of_int (14)))
      (Obj.magic (FStar_Reflection_Formula.term_as_formula' t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Formula.False_ ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> true)))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                           (Prims.of_int (181)) (Prims.of_int (23))
                           (Prims.of_int (181)) (Prims.of_int (32)))
                        (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                           (Prims.of_int (181)) (Prims.of_int (17))
                           (Prims.of_int (191)) (Prims.of_int (23)))
                        (Obj.magic (FStar_Tactics_Builtins.inspect t))
                        (fun uu___2 ->
                           (fun uu___2 ->
                              match uu___2 with
                              | FStar_Reflection_Data.Tv_App (l, r) ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Tactics.Simplifier.fst"
                                             (Prims.of_int (183))
                                             (Prims.of_int (24))
                                             (Prims.of_int (183))
                                             (Prims.of_int (33)))
                                          (Prims.mk_range
                                             "FStar.Tactics.Simplifier.fst"
                                             (Prims.of_int (183))
                                             (Prims.of_int (18))
                                             (Prims.of_int (189))
                                             (Prims.of_int (24)))
                                          (Obj.magic
                                             (FStar_Tactics_Builtins.inspect
                                                l))
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                match uu___3 with
                                                | FStar_Reflection_Data.Tv_Abs
                                                    (b, t1) ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Simplifier.fst"
                                                               (Prims.of_int (185))
                                                               (Prims.of_int (28))
                                                               (Prims.of_int (185))
                                                               (Prims.of_int (46)))
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Simplifier.fst"
                                                               (Prims.of_int (185))
                                                               (Prims.of_int (22))
                                                               (Prims.of_int (187))
                                                               (Prims.of_int (28)))
                                                            (Obj.magic
                                                               (FStar_Reflection_Formula.term_as_formula'
                                                                  t1))
                                                            (fun uu___4 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___5
                                                                    ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Formula.False_
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
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (197))
         (Prims.of_int (12)) (Prims.of_int (197)) (Prims.of_int (23)))
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (198))
         (Prims.of_int (4)) (Prims.of_int (205)) (Prims.of_int (18)))
      (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
      (fun uu___1 ->
         (fun t ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                    (Prims.of_int (198)) (Prims.of_int (10))
                    (Prims.of_int (198)) (Prims.of_int (19)))
                 (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                    (Prims.of_int (198)) (Prims.of_int (4))
                    (Prims.of_int (205)) (Prims.of_int (18)))
                 (Obj.magic (FStar_Tactics_Builtins.inspect t))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       match uu___1 with
                       | FStar_Reflection_Data.Tv_FVar fv ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (Prims.mk_range
                                      "FStar.Tactics.Simplifier.fst"
                                      (Prims.of_int (200))
                                      (Prims.of_int (17))
                                      (Prims.of_int (200))
                                      (Prims.of_int (30)))
                                   (Prims.mk_range
                                      "FStar.Tactics.Simplifier.fst"
                                      (Prims.of_int (201))
                                      (Prims.of_int (13))
                                      (Prims.of_int (204))
                                      (Prims.of_int (20)))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         FStar_Reflection_Builtins.inspect_fv
                                           fv))
                                   (fun uu___2 ->
                                      (fun qn ->
                                         if
                                           qn =
                                             FStar_Reflection_Const.int_lid
                                         then
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_Derived.exact
                                                   (FStar_Reflection_Builtins.pack_ln
                                                      (FStar_Reflection_Data.Tv_Const
                                                         (FStar_Reflection_Data.C_Int
                                                            (Prims.of_int (42)))))))
                                         else
                                           Obj.magic
                                             (Obj.repr
                                                (if
                                                   qn =
                                                     FStar_Reflection_Const.bool_lid
                                                 then
                                                   Obj.repr
                                                     (FStar_Tactics_Derived.exact
                                                        (FStar_Reflection_Builtins.pack_ln
                                                           (FStar_Reflection_Data.Tv_Const
                                                              FStar_Reflection_Data.C_True)))
                                                 else
                                                   Obj.repr
                                                     (if
                                                        qn =
                                                          FStar_Reflection_Const.unit_lid
                                                      then
                                                        Obj.repr
                                                          (FStar_Tactics_Derived.exact
                                                             (FStar_Reflection_Builtins.pack_ln
                                                                (FStar_Reflection_Data.Tv_Const
                                                                   FStar_Reflection_Data.C_Unit)))
                                                      else
                                                        Obj.repr
                                                          (FStar_Tactics_Derived.fail
                                                             ""))))) uu___2)))
                       | uu___2 ->
                           Obj.magic
                             (Obj.repr (FStar_Tactics_Derived.fail "")))
                      uu___1))) uu___1)
let rec (simplify_point : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (211))
         (Prims.of_int (4)) (Prims.of_int (211)) (Prims.of_int (14)))
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (212))
         (Prims.of_int (4)) (Prims.of_int (266)) (Prims.of_int (81)))
      (Obj.magic (recurse ()))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                    (Prims.of_int (212)) (Prims.of_int (4))
                    (Prims.of_int (212)) (Prims.of_int (11)))
                 (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                    (Prims.of_int (213)) (Prims.of_int (4))
                    (Prims.of_int (266)) (Prims.of_int (81)))
                 (Obj.magic (FStar_Tactics_Builtins.norm []))
                 (fun uu___2 ->
                    (fun uu___2 ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                               (Prims.of_int (213)) (Prims.of_int (12))
                               (Prims.of_int (213)) (Prims.of_int (23)))
                            (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                               (Prims.of_int (214)) (Prims.of_int (4))
                               (Prims.of_int (266)) (Prims.of_int (81)))
                            (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                            (fun uu___3 ->
                               (fun g ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (Prims.mk_range
                                          "FStar.Tactics.Simplifier.fst"
                                          (Prims.of_int (214))
                                          (Prims.of_int (12))
                                          (Prims.of_int (214))
                                          (Prims.of_int (29)))
                                       (Prims.mk_range
                                          "FStar.Tactics.Simplifier.fst"
                                          (Prims.of_int (215))
                                          (Prims.of_int (4))
                                          (Prims.of_int (266))
                                          (Prims.of_int (81)))
                                       (Obj.magic
                                          (FStar_Reflection_Formula.term_as_formula
                                             g))
                                       (fun uu___3 ->
                                          (fun f ->
                                             match f with
                                             | FStar_Reflection_Formula.Iff
                                                 (l, r) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Simplifier.fst"
                                                            (Prims.of_int (217))
                                                            (Prims.of_int (20))
                                                            (Prims.of_int (217))
                                                            (Prims.of_int (38)))
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Simplifier.fst"
                                                            (Prims.of_int (217))
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (264))
                                                            (Prims.of_int (22)))
                                                         (Obj.magic
                                                            (FStar_Reflection_Formula.term_as_formula'
                                                               l))
                                                         (fun uu___3 ->
                                                            (fun uu___3 ->
                                                               match uu___3
                                                               with
                                                               | FStar_Reflection_Formula.And
                                                                   (p, q) ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_and_p"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_and_true"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_and_p"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
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
                                                               | FStar_Reflection_Formula.Or
                                                                   (p, q) ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_or_p"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_or_true"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_or_p"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
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
                                                               | FStar_Reflection_Formula.Implies
                                                                   (p, q) ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_imp_p"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_imp_true"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
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
                                                               | FStar_Reflection_Formula.Forall
                                                                   (b, p) ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_fa_true"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.or_else
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (82)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (94)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
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
                                                               | FStar_Reflection_Formula.Exists
                                                                   (b, p) ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_ex_false"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.or_else
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (81)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (93)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
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
                                                               | FStar_Reflection_Formula.Not
                                                                   p ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_neg_true"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_neg_false"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (tiff ()))
                                                                    uu___6)))
                                                                    uu___4))
                                                               | FStar_Reflection_Formula.Iff
                                                                   (p, q) ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (19)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (step ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (24)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_true_iff_p"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_p_iff_true"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "lem_false_iff_p"]))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (30)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (24)))
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
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
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
                                                      (FStar_Tactics_Derived.fail
                                                         "simplify_point: failed precondition: goal should be `g <==> ?u`")))
                                            uu___3))) uu___3))) uu___2)))
           uu___1)
and (recurse : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (269))
         (Prims.of_int (4)) (Prims.of_int (269)) (Prims.of_int (11)))
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (270))
         (Prims.of_int (4)) (Prims.of_int (304)) (Prims.of_int (74)))
      (Obj.magic (step ()))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                    (Prims.of_int (270)) (Prims.of_int (4))
                    (Prims.of_int (270)) (Prims.of_int (11)))
                 (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                    (Prims.of_int (271)) (Prims.of_int (4))
                    (Prims.of_int (304)) (Prims.of_int (74)))
                 (Obj.magic (FStar_Tactics_Builtins.norm []))
                 (fun uu___2 ->
                    (fun uu___2 ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                               (Prims.of_int (271)) (Prims.of_int (12))
                               (Prims.of_int (271)) (Prims.of_int (23)))
                            (Prims.mk_range "FStar.Tactics.Simplifier.fst"
                               (Prims.of_int (272)) (Prims.of_int (4))
                               (Prims.of_int (304)) (Prims.of_int (74)))
                            (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                            (fun uu___3 ->
                               (fun g ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (Prims.mk_range
                                          "FStar.Tactics.Simplifier.fst"
                                          (Prims.of_int (272))
                                          (Prims.of_int (12))
                                          (Prims.of_int (272))
                                          (Prims.of_int (29)))
                                       (Prims.mk_range
                                          "FStar.Tactics.Simplifier.fst"
                                          (Prims.of_int (273))
                                          (Prims.of_int (4))
                                          (Prims.of_int (304))
                                          (Prims.of_int (74)))
                                       (Obj.magic
                                          (FStar_Reflection_Formula.term_as_formula
                                             g))
                                       (fun uu___3 ->
                                          (fun f ->
                                             match f with
                                             | FStar_Reflection_Formula.Iff
                                                 (l, r) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Simplifier.fst"
                                                            (Prims.of_int (275))
                                                            (Prims.of_int (20))
                                                            (Prims.of_int (275))
                                                            (Prims.of_int (38)))
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Simplifier.fst"
                                                            (Prims.of_int (275))
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (302))
                                                            (Prims.of_int (22)))
                                                         (Obj.magic
                                                            (FStar_Reflection_Formula.term_as_formula'
                                                               l))
                                                         (fun uu___3 ->
                                                            (fun uu___3 ->
                                                               match uu___3
                                                               with
                                                               | FStar_Reflection_Formula.And
                                                                   (uu___4,
                                                                    uu___5)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Derived.seq
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "and_cong"]))))
                                                                    simplify_point)
                                                               | FStar_Reflection_Formula.Or
                                                                   (uu___4,
                                                                    uu___5)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Derived.seq
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "or_cong"]))))
                                                                    simplify_point)
                                                               | FStar_Reflection_Formula.Implies
                                                                   (uu___4,
                                                                    uu___5)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Derived.seq
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "imp_cong"]))))
                                                                    simplify_point)
                                                               | FStar_Reflection_Formula.Forall
                                                                   (uu___4,
                                                                    uu___5)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (34)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "fa_cong"])))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (28)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.intro
                                                                    ()))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (simplify_point
                                                                    ()))
                                                                    uu___7)))
                                                                    uu___6))
                                                               | FStar_Reflection_Formula.Exists
                                                                   (uu___4,
                                                                    uu___5)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (34)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Simplifier";
                                                                    "ex_cong"])))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (28)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.intro
                                                                    ()))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (simplify_point
                                                                    ()))
                                                                    uu___7)))
                                                                    uu___6))
                                                               | FStar_Reflection_Formula.Not
                                                                   uu___4 ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Simplifier.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
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
                                                               | FStar_Reflection_Formula.Iff
                                                                   (uu___4,
                                                                    uu___5)
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Derived.seq
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
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
                                                      (FStar_Tactics_Derived.fail
                                                         "recurse: failed precondition: goal should be `g <==> ?u`")))
                                            uu___3))) uu___3))) uu___2)))
           uu___1)
let (simplify : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (310))
         (Prims.of_int (4)) (Prims.of_int (310)) (Prims.of_int (24)))
      (Prims.mk_range "FStar.Tactics.Simplifier.fst" (Prims.of_int (311))
         (Prims.of_int (4)) (Prims.of_int (311)) (Prims.of_int (21)))
      (Obj.magic
         (FStar_Tactics_Derived.apply_lemma
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Simplifier"; "equiv"])))))
      (fun uu___1 -> (fun uu___1 -> Obj.magic (simplify_point ())) uu___1)